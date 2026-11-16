/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Parabolic.Basic
public import TauCeti.Algebra.AlgebraicGroup.Borel.ProjectiveOrbit
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Proper
import TauCeti.Algebra.AlgebraicGroup.Borel.Existence
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# Proper homogeneous quotients and parabolic subgroups

Let `G` be an affine group of finite type over an algebraically closed field `k`, with coordinate
Hopf algebra `H`, and let `P` be a smooth closed subgroup cut out by a Hopf ideal `I`.

When `P` is the rational-point stabilizer of the base point `[m]` in a projective orbit whose
structural morphism `Comodule.projectiveOrbitToSpec` is proper over `Spec k`, the orbit image in
projective space is closed. Any Borel subgroup `B` of `G` is smooth, connected, and solvable, so by
the Borel fixed-point theorem (`HopfIdeal.exists_conjugate_le_of_isClosed_projectiveOrbit`) it fixes
a rational point of the closed orbit and therefore lies in a conjugate of `P`. Conjugating back
exhibits a Borel subgroup inside `P`, proving that `P` is parabolic. Neither reducedness nor
connectedness of `G` is needed when a projective orbit with rational-point stabilizer `P` is given.

When `G` is reduced, every closed subgroup `P` has a Chevalley projective orbit representing the
fppf homogeneous quotient `G / P`, and properness over `Spec k` is independent of the choice of
representing scheme (`CommHopfAlgCat.isProper_hom_iff_of_fppfHomogeneousQuotientIso`). Hence a
smooth closed subgroup `P` whose homogeneous quotient `G / P` is represented by a proper scheme over
`Spec k` is parabolic (the proper-implies-parabolic half of Milne, Theorem 17.16).

Conversely, if `B` is a Borel subgroup of `G` whose homogeneous quotient `G / B` is represented by a
proper scheme over `Spec k`, then for every parabolic subgroup `P` some conjugate `g P g⁻¹` contains
`B`, so the surjective quotient morphism `G / B ⟶ G / (g P g⁻¹)` descends properness to
`G / (g P g⁻¹)` and conjugation transports it back to `G / P`. Thus, given properness of one Borel
quotient, a smooth closed subgroup `P` is parabolic if and only if `G / P` is proper over `Spec k`.

## Main declarations

* `TauCeti.HopfIdeal.isParabolicOverAlgClosed_of_isClosed_projectiveOrbit`: a smooth closed subgroup
  that is the rational-point stabilizer of a closed projective orbit is parabolic.
* `TauCeti.HopfIdeal.isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec`: a smooth closed
  subgroup that is the rational-point stabilizer of a proper projective orbit scheme is parabolic.
* `TauCeti.HopfIdeal.isParabolicOverAlgClosed_of_isProper_fppfHomogeneousQuotientIso`: **proper
  homogeneous space implies parabolic** (Milne, Theorem 17.16): for reduced `G`, if a scheme
  representing `G / P` is proper over `Spec k` and `P` is smooth, then `P` is parabolic.
* `TauCeti.HopfIdeal.isParabolicOverAlgClosed_of_isProper_fppfHomogeneousQuotientIso_of_charZero`:
  in characteristic zero, Cartier's theorem supplies reducedness of `G` and smoothness of `P`
  automatically.
* `TauCeti.HopfIdeal.IsParabolicOverAlgClosed.isProper_of_borel`: given a Borel subgroup with proper
  homogeneous quotient, every parabolic subgroup has proper homogeneous quotient.
* `TauCeti.HopfIdeal.isProper_hom_iff_isParabolicOverAlgClosed_of_borel` and
  `TauCeti.HopfIdeal.isProper_projectiveOrbitToSpec_iff_isParabolicOverAlgClosed_of_borel`: the full
  equivalence between properness of `G / P` and parabolicity of smooth `P`, given one proper Borel
  quotient.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.16, p. 356.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.2, Corollary.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv

namespace TauCeti.HopfIdeal

universe u

section GivenOrbit

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H]
  {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- **Closed projective orbit implies parabolic.** Over an algebraically closed field `k`, if a
smooth closed subgroup `P` (cut out by `I`) is the rational-point stabilizer of the base point `[m]`
of a closed projective orbit, then `P` is parabolic. Neither reducedness nor connectedness of the
ambient group is needed. -/
theorem isParabolicOverAlgClosed_of_isClosed_projectiveOrbit (I : HopfIdeal k H)
    (hI : smoothCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) I).obj)
    (m : M) (hm : Module.IsUnimodular k m)
    (hclosed : IsClosed (Set.range (Comodule.projectiveOrbitMap (H := H) m hm)))
    (hstab : ∀ a : WithConv (H →ₐ[k] k),
      a ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k) ↔
        Comodule.projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
          Comodule.projectiveOrbitMap (H := H) m hm
            (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))) :
    IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I := by
  obtain ⟨B, hBmin⟩ := exists_minimal_isBorelCandidate (FiniteTypeCommHopfAlgCat.of k H)
  have hB : IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) B :=
    (isBorelOverAlgClosed_iff _ _ _).mpr ⟨inferInstance, hBmin⟩
  obtain ⟨g, hg⟩ := hBmin.prop.exists_conjugate_le fun J _ _ _ ↦
    exists_conjugate_le_of_isClosed_projectiveOrbit
      (H := FiniteTypeCommHopfAlgCat.of k H) I J m hm hclosed hstab
  exact (isParabolicOverAlgClosed_iff_exists_conjugate_le hB).mpr ⟨hI, g, hg⟩

/-- **Proper projective orbit implies parabolic.** Over an algebraically closed field `k`, if a
smooth closed subgroup `P` is the rational-point stabilizer of the base point `[m]` of a projective
orbit scheme that is proper over `Spec k`, then `P` is parabolic. Neither reducedness nor
connectedness of the ambient group is needed. -/
theorem isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec (I : HopfIdeal k H)
    (hI : smoothCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) I).obj)
    (m : M) (hm : Module.IsUnimodular k m)
    [IsProper (Comodule.projectiveOrbitToSpec (H := H) m hm)]
    (hstab : ∀ a : WithConv (H →ₐ[k] k),
      a ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k) ↔
        Comodule.projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
          Comodule.projectiveOrbitMap (H := H) m hm
            (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))) :
    IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I :=
  isParabolicOverAlgClosed_of_isClosed_projectiveOrbit I hI m hm
    ((Comodule.isProper_projectiveOrbitToSpec_iff_isClosed_range (H := H) m hm).mp inferInstance)
    hstab

/-- Over an algebraically closed field `k`, if the matrix coefficients at a unimodular vector `m`
detect the left cosets of a smooth closed subgroup `P` and the projective orbit scheme of `[m]` is
proper over `Spec k`, then `P` is parabolic. -/
theorem isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec_of_coset (I : HopfIdeal k H)
    (hI : smoothCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) I).obj)
    (m : M) (hm : Module.IsUnimodular k m)
    [IsProper (Comodule.projectiveOrbitToSpec (H := H) m hm)]
    (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M,
          h.ofConv (Comodule.matrixCoefficient (C := H) φ m) =
            c * g.ofConv (Comodule.matrixCoefficient (C := H) φ m)) :
    IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I :=
  isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec I hI m hm
    (Comodule.mem_quotientPointsSubgroup_iff_projectiveOrbitMap_kernelPoint_eq I m hm hcoset)

end GivenOrbit

section RepresentingScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H]

/-- **Proper homogeneous quotient implies parabolic (Milne, Theorem 17.16).** Let `G` be a reduced
affine group of finite type over an algebraically closed field `k`, and let `P` be a smooth closed
subgroup cut out by `I`. If any scheme `X` over `Spec k` representing `G / P` is proper over
`Spec k`, then `P` is parabolic. -/
theorem isParabolicOverAlgClosed_of_isProper_fppfHomogeneousQuotientIso [_root_.IsReduced H]
    (I : HopfIdeal k H)
    (hI : smoothCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) I).obj)
    {X : Over (Spec (CommRingCat.of k))}
    (e : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    [IsProper X.hom] :
    IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I := by
  obtain ⟨M, _, _, _, _, m₀, hm₀, hcoset, ⟨e₀⟩⟩ :=
    I.exists_coset_matrixCoefficient_fppfHomogeneousQuotientIsoPointsSheaf
  have _ : IsProper (Comodule.projectiveOrbitToSpec (H := H) m₀ hm₀) :=
    (CommHopfAlgCat.isProper_hom_iff_of_fppfHomogeneousQuotientIso H I e e₀).mp inferInstance
  exact isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec_of_coset I hI m₀ hm₀ hcoset

/-- In characteristic zero, Cartier's theorem makes both the ambient group and every closed subgroup
smooth and reduced, so any closed subgroup whose homogeneous quotient `G / P` is represented by a
proper scheme over `Spec k` is parabolic. -/
theorem isParabolicOverAlgClosed_of_isProper_fppfHomogeneousQuotientIso_of_charZero [CharZero k]
    (I : HopfIdeal k H) {X : Over (Spec (CommRingCat.of k))}
    (e : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    [IsProper X.hom] :
    IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I := by
  let _ : _root_.IsReduced H := HopfAlgebra.isReduced_of_charZero k H
  exact isParabolicOverAlgClosed_of_isProper_fppfHomogeneousQuotientIso I
    (smoothCommHopfAlgProperty_of_charZero k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) I).obj)
    e

/-- **Parabolic homogeneous spaces inherit properness from a Borel quotient.** Over an
algebraically closed field `k`, if `G` is reduced and `B` is a Borel subgroup whose fppf homogeneous
quotient `G / B` is represented by a proper scheme over `Spec k`, then for every parabolic subgroup
`P` any scheme representing `G / P` is proper over `Spec k`. -/
theorem IsParabolicOverAlgClosed.isProper_of_borel [_root_.IsReduced H]
    {I B : HopfIdeal k H}
    (hI : IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I)
    (hB : IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) B)
    {XB X : Over (Spec (CommRingCat.of k))}
    (eB : CommHopfAlgCat.fppfHomogeneousQuotient H B ≅ CommAlgCat.pointsSheaf XB)
    [IsProper XB.hom]
    (eI : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    IsProper X.hom := by
  obtain ⟨g, hg⟩ := hI.exists_conjugate_le hB
  exact CommHopfAlgCat.isProper_of_fppfHomogeneousQuotientIso_of_le H eB
    (CommHopfAlgCat.fppfHomogeneousQuotientConjugateRepresentingIso H I eI g) hg

/-- **Milne, Theorem 17.16 (given a proper Borel quotient).** Let `G` be a reduced affine group of
finite type over an algebraically closed field `k`, and assume a Borel subgroup `B` has a proper
representing scheme for `G / B`. For any smooth closed subgroup `P` cut out by `I` and any scheme
`X` over `Spec k` representing `G / P`, `X` is proper over `Spec k` if and only if `P` is
parabolic. -/
theorem isProper_hom_iff_isParabolicOverAlgClosed_of_borel [_root_.IsReduced H]
    {I B : HopfIdeal k H}
    (hI : smoothCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) I).obj)
    (hB : IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) B)
    {XB X : Over (Spec (CommRingCat.of k))}
    (eB : CommHopfAlgCat.fppfHomogeneousQuotient H B ≅ CommAlgCat.pointsSheaf XB)
    [IsProper XB.hom]
    (eI : CommHopfAlgCat.fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    IsProper X.hom ↔
      IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I :=
  ⟨fun _ ↦ isParabolicOverAlgClosed_of_isProper_fppfHomogeneousQuotientIso I hI eI,
    fun h ↦ h.isProper_of_borel hB eB eI⟩

/-- **Projective-orbit form of Milne, Theorem 17.16 (given a proper Borel quotient).** Let `G` be a
reduced affine group of finite type over an algebraically closed field `k`, and assume a Borel
subgroup `B` has a proper representing scheme for `G / B`. For any smooth closed subgroup `P` whose
left cosets are detected by the matrix coefficients at a unimodular vector `m`, the projective orbit
scheme of `[m]` is proper over `Spec k` if and only if `P` is parabolic. -/
theorem isProper_projectiveOrbitToSpec_iff_isParabolicOverAlgClosed_of_borel [_root_.IsReduced H]
    {I B : HopfIdeal k H}
    (hI : smoothCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) I).obj)
    (hB : IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) B)
    {XB : Over (Spec (CommRingCat.of k))}
    (eB : CommHopfAlgCat.fppfHomogeneousQuotient H B ≅ CommAlgCat.pointsSheaf XB)
    [IsProper XB.hom]
    {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
    (m : M) (hm : Module.IsUnimodular k m)
    (hcoset : ∀ (A : CommAlgCat.{u} k) (g h : HopfAlgebra.points (R := k) (H := H) A),
      (QuotientGroup.mk g : HopfAlgebra.points (R := k) (H := H) A ⧸
          CommHopfAlgCat.quotientPointsSubgroup H I A) = QuotientGroup.mk h ↔
        ∃ c : Aˣ, ∀ φ : Module.Dual k M,
          h.ofConv (Comodule.matrixCoefficient (C := H) φ m) =
            c * g.ofConv (Comodule.matrixCoefficient (C := H) φ m)) :
    IsProper (Comodule.projectiveOrbitToSpec (H := H) m hm) ↔
      IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I :=
  isProper_hom_iff_isParabolicOverAlgClosed_of_borel hI hB eB
    (Comodule.fppfHomogeneousQuotientIsoPointsSheafProjectiveOrbit I m hm hcoset)

end RepresentingScheme

end TauCeti.HopfIdeal
