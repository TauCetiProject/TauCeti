/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Intertwining
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists

/-!
# Eigensystems on finite Riesz summands

A pairwise commuting family of linear endomorphisms commuting with a row-compact operator
has a common eigenvector in every nonzero Riesz summand on which the family splits. Only
the restrictions to this finite-dimensional summand need be triangularizable. The ambient
space and the family may be infinite.
The commuting endomorphisms need not be continuous.

For an action of a commutative algebra, the eigenvalues form an algebra homomorphism.
Over an algebraically closed coefficient field the splitting hypothesis is automatic.
The results apply to any nonzero Riesz projection, without choosing the order of a
Fredholm zero, a basis, or generators for the commuting algebra.

The finite-dimensional input is `TauCeti.exists_jointEigenvector_of_pairwise_commute`;
`AlgHom.eigenvalueHomOfJointEigenvector` packages the resulting eigenvalue function.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A4.
-/

public section

open scoped ZeroAtInfty

namespace ContinuousLinearMap.IsRieszProjection

variable {I K : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {u E : C₀(I, K) →L[K] C₀(I, K)} {a : K} {h : ℕ}

/-- A commuting family has a common eigenvector in a nonzero Riesz summand whenever its
restrictions to that summand are triangularizable. The index type may be infinite or empty,
and continuity of the commuting maps is unnecessary. -/
theorem exists_jointEigenvector (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact)
    (hE0 : E ≠ 0) {ι : Type*} (f : ι → Module.End K C₀(I, K))
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hfu : ∀ i, Function.Semiconj (f i) u u)
    (htri : ∀ i, ⨆ μ, Module.End.maxGenEigenspace (R := K) (M := E.range) ((f i).restrict
      (hE.mapsTo_range_of_semiconj hE (f i) (hfu i))) μ = ⊤) :
    ∃ (χ : ι → K) (v : C₀(I, K)), v ≠ 0 ∧ v ∈ E.range ∧
      ∀ i, f i v = χ i • v := by
  let := (hE.isRowCompact hu).finite_range_of_isIdempotentElem hE.isIdempotentElem
  have hrange : E.range ≠ ⊥ := by
    intro hz
    apply hE0
    exact ContinuousLinearMap.coe_injective (LinearMap.range_eq_bot.mp hz)
  let : Nontrivial E.range := Submodule.nontrivial_iff_ne_bot.mpr hrange
  let g : ι → Module.End K E.range := fun i ↦
    (f i).restrict (hE.mapsTo_range_of_semiconj hE (f i) (hfu i))
  have hg : Pairwise fun i j ↦ Commute (g i) (g j) := fun i j hij ↦
    LinearMap.restrict_commute (hcomm hij) _ _
  obtain ⟨χ, v, hv, heigen⟩ :=
    TauCeti.exists_jointEigenvector_of_pairwise_commute (K := K) (V := E.range) g hg htri
  refine ⟨χ, v, Submodule.coe_eq_zero.not.mpr hv, v.property, fun i ↦ ?_⟩
  exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp (heigen i))

/-- Over an algebraically closed field, a commuting family has a common eigenvector in
every nonzero Riesz summand of a row-compact operator. -/
theorem exists_jointEigenvector_of_isAlgClosed [IsAlgClosed K]
    (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact) (hE0 : E ≠ 0)
    {ι : Type*} (f : ι → Module.End K C₀(I, K))
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hfu : ∀ i, Function.Semiconj (f i) u u) :
    ∃ (χ : ι → K) (v : C₀(I, K)), v ≠ 0 ∧ v ∈ E.range ∧
      ∀ i, f i v = χ i • v := by
  let := (hE.isRowCompact hu).finite_range_of_isIdempotentElem hE.isIdempotentElem
  exact hE.exists_jointEigenvector hu hE0 f hcomm hfu
    (fun _ ↦ Module.End.iSup_maxGenEigenspace_eq_top _)

/-- A commutative algebra acting by endomorphisms commuting with `u` has an eigensystem
in every nonzero Riesz summand on which its action splits. The eigensystem is an algebra
homomorphism, so it preserves all algebra relations, not just a chosen list of generators. -/
theorem exists_eigenvalueHom (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact)
    (hE0 : E ≠ 0) {A : Type*} [CommSemiring A] [Algebra K A]
    (ρ : A →ₐ[K] Module.End K C₀(I, K))
    (hρu : ∀ b, Function.Semiconj (ρ b) u u)
    (htri : ∀ b, ⨆ μ, Module.End.maxGenEigenspace (R := K) (M := E.range) ((ρ b).restrict
      (hE.mapsTo_range_of_semiconj hE (ρ b) (hρu b))) μ = ⊤) :
    ∃ (χ : A →ₐ[K] K) (v : C₀(I, K)), v ≠ 0 ∧ v ∈ E.range ∧
      ∀ b, ρ b v = χ b • v := by
  have hcomm : Pairwise fun b c ↦ Commute (ρ b) (ρ c) := fun b c _ ↦
    (Commute.all b c).map ρ
  obtain ⟨χ, v, hv, hvr, heigen⟩ := hE.exists_jointEigenvector hu hE0 ρ hcomm hρu htri
  have hmem (b : A) : v ∈ (ρ b).eigenspace (χ b) :=
    Module.End.mem_eigenspace_iff.mpr (heigen b)
  refine ⟨ρ.eigenvalueHomOfJointEigenvector χ v hv hmem, v, hv, hvr, fun b ↦ ?_⟩
  simpa only [AlgHom.eigenvalueHomOfJointEigenvector_apply] using heigen b

/-- Over an algebraically closed coefficient field, every commutative algebra action
commuting with a row-compact operator has a scalar eigensystem in each nonzero
Riesz summand. -/
theorem exists_eigenvalueHom_of_isAlgClosed [IsAlgClosed K]
    (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact) (hE0 : E ≠ 0)
    {A : Type*} [CommSemiring A] [Algebra K A] (ρ : A →ₐ[K] Module.End K C₀(I, K))
    (hρu : ∀ b, Function.Semiconj (ρ b) u u) :
    ∃ (χ : A →ₐ[K] K) (v : C₀(I, K)), v ≠ 0 ∧ v ∈ E.range ∧
      ∀ b, ρ b v = χ b • v := by
  let := (hE.isRowCompact hu).finite_range_of_isIdempotentElem hE.isIdempotentElem
  exact hE.exists_eigenvalueHom hu hE0 ρ hρu
    (fun _ ↦ Module.End.iSup_maxGenEigenspace_eq_top _)

end ContinuousLinearMap.IsRieszProjection
