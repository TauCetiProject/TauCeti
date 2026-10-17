/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Torsion.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Torsion.Free
import TauCeti.RingTheory.PowerSeries.Evaluation

/-!
# Division by a unit in the elliptic formal group

Multiplication by an integer invertible in the coefficient ring is an automorphism of the
elliptic formal group evaluated on an adic ideal. Its inverse is obtained by evaluating the
compositional inverse of the multiplication series, whose linear coefficient is that integer.
Mathlib's `PowerSeries.substInvOfIsUnit` supplies this inverse; the existing
`FormalGroupPoint.coe_nsmul` identifies the evaluated multiplication series with scalar
multiplication on formal parameters.
Consequently the kernel of reduction over a completed discretely valued field is uniquely
divisible by integers prime to the residue characteristic. This supplies torsion lifts under
good reduction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.3.2 and VII.3.1.
-/

public section

namespace WeierstrassCurve

namespace FormalGroupPoint

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]
  {W : WeierstrassCurve O} {I : Ideal O} [Fact (IsAdic I)]

open MvPowerSeries.WithPiTopology in
/-- Multiplication by an integer invertible in the coefficient ring is surjective on the
formal group evaluated on an adic ideal. -/
theorem nsmul_surjective {n : ℕ} (hn : IsUnit (n : O)) :
    Function.Surjective (fun P : FormalGroupPoint W I ↦ n • P) := by
  intro P
  let S := (formalGroup W).nsmulSeries n
  have hS : PowerSeries.constantCoeff S = 0 := (formalGroup W).constantCoeff_nsmulSeries n
  have hunit : IsUnit (PowerSeries.coeff 1 S) := by
    simpa [S] using hn
  let Q := S.substInvOfIsUnit hunit
  have hQ : PowerSeries.constantCoeff Q = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hmem : PowerSeries.aeval (R := O) P.hasEval Q ∈ I := by
    have h := MvPowerSeries.eval₂_mem_pow (φ := RingHom.id O) continuous_id
      (PowerSeries.hasEval P.hasEval) (Fact.out : IsAdic I) (k := 1)
      (fun _ ↦ by simpa using P.property) Q (by simp [← PowerSeries.constantCoeff_eq, hQ])
    simpa [PowerSeries.coe_aeval, PowerSeries.eval₂, Algebra.algebraMap_self] using h
  let P' : FormalGroupPoint W I := ⟨PowerSeries.aeval P.hasEval Q, hmem⟩
  refine ⟨P', FormalGroupPoint.ext ?_⟩
  have h := congrArg (PowerSeries.aeval (R := O) P.hasEval)
    (PowerSeries.subst_substInvOfIsUnit_right S hS hunit)
  rw [PowerSeries.aeval_subst (PowerSeries.HasSubst.of_constantCoeff_zero hQ)
    (PowerSeries.continuous_aeval P.hasEval) P'.hasEval, PowerSeries.aeval_X] at h
  simpa only [coe_nsmul, PowerSeries.coe_aeval, Algebra.algebraMap_self, P', S] using h

/-- Multiplication by an integer invertible in the coefficient ring is bijective on the
formal group evaluated on an adic ideal. -/
theorem nsmul_bijective {n : ℕ} (hn : IsUnit (n : O)) :
    Function.Bijective (fun P : FormalGroupPoint W I ↦ n • P) := by
  refine ⟨?_, nsmul_surjective hn⟩
  intro P Q h
  dsimp only at h
  exact sub_eq_zero.mp (eq_zero_of_nsmul_eq_zero hn (by rw [nsmul_sub, h, sub_self]))

end FormalGroupPoint

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A)
  (C : WeierstrassCurve (u.adicCompletionIntegers F))
  [(C.baseChange (u.adicCompletion F)).IsElliptic]

local instance : IsLinearTopology (u.adicCompletionIntegers F) (u.adicCompletionIntegers F) :=
  u.isAdic_maximalIdeal_adicCompletionIntegers (K := F) ▸
    Ideal.isLinearTopology (IsLocalRing.maximalIdeal (u.adicCompletionIntegers F))

local instance : Fact (IsAdic (IsLocalRing.maximalIdeal (u.adicCompletionIntegers F))) :=
  ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)⟩

open scoped Classical in
/-- The kernel of reduction is uniquely divisible by integers prime to the residue
characteristic. -/
theorem nsmul_kerReduction_bijective {n : ℕ} (hn : (n : A) ∉ u.asIdeal) :
    Function.Bijective (fun P : C.kerReduction u ↦ n • P) := by
  have hunit : IsUnit (n : u.adicCompletionIntegers F) := by
    simpa using (u.isUnit_algebraMap_adicCompletionIntegers_iff (K := F) (n : A)).mpr hn
  let e := C.formalPointAddEquivKerReduction u
  constructor
  · intro P Q h
    apply e.symm.injective
    exact (FormalGroupPoint.nsmul_bijective hunit).1 (by simpa using congrArg e.symm h)
  · intro P
    obtain ⟨Q, hQ⟩ := (FormalGroupPoint.nsmul_bijective hunit).2 (e.symm P)
    exact ⟨e Q, by simpa using congrArg e hQ⟩

end WeierstrassCurve
