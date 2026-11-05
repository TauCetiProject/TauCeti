/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.ClassTwo
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points

/-!
# Central-bracket root subgroups in the toral Kostant carrier

The matrix image of `kostantBracketRootSubgroupParam` lies in the toral-closure points:
the class-two Chevalley relation expresses each of its elements as a commutator of two
of the original root-subgroup points. This gives a sum-root subgroup without adding the
bracket to the distinguished generators. The relation is transported from
`commutatorElement_kostantRootSubgroupParam_eq_bracket` and holds over every commutative ring.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

open WithConv
open scoped commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
  {I : Type w} {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module ℚ V]
  (e : I → L) (h : κ → L)
  (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
  (M : AddSubgroup V)
  (hM : ∀ a ∈ kostantForm e h, ∀ v ∈ M, ρ a v ∈ M)
  (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
  {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)
  {i j : I}

variable (hi : ⁅e i, ⁅e i, e j⁆⁆ = 0) (hj : ⁅e j, ⁅e i, e j⁆⁆ = 0)

private theorem commutator_eq_matrix_bracket (A : Type v) [CommRing A] (a c : A) :
    ((⁅kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A (Multiplicative.ofAdd a),
        kostantToralRootSubgroupPoints e h ρ M hM hnil b wt j A (Multiplicative.ofAdd c)⁆ :
      kostantToralPointsSubgroup e h ρ M hM hnil b wt A) :
        Matrix.GeneralLinearGroup (Fin n) A) =
      Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom
        (kostantBracketRootSubgroupParam e h ρ M hM hi hj (hnil i) (CommAlgCat.of ℤ A)
          (Multiplicative.ofAdd (a * c))) := by
  have heq := commutatorElement_kostantRootSubgroupParam_eq_bracket e h ρ M hM hi hj
    (hnil i) (hnil j) (CommAlgCat.of ℤ A) a c
  have hm := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom) heq
  simpa only [commutatorElement_def, map_mul, map_inv,
    matrix_kostantRootSubgroupParam e h ρ M hM hnil b wt,
    Subgroup.coe_mul, Subgroup.coe_inv] using hm

/-- The central-bracket exponential as a one-parameter subgroup of the toral Kostant carrier.
Its normalization is the ordered bracket of the two distinguished root vectors. -/
noncomputable def kostantToralBracketRootSubgroupPoints (A : Type v) [CommRing A] :
    Multiplicative A →* kostantToralPointsSubgroup e h ρ M hM hnil b wt A :=
  MonoidHom.codRestrict
    ((Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom).comp
      (kostantBracketRootSubgroupParam e h ρ M hM hi hj (hnil i) (CommAlgCat.of ℤ A)))
    (kostantToralPointsSubgroup e h ρ M hM hnil b wt A) fun a ↦ by
      have heq := commutator_eq_matrix_bracket e h ρ M hM hnil b wt hi hj A a.toAdd 1
      simp only [mul_one, ofAdd_toAdd] at heq
      exact heq ▸ (⁅kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A a,
        kostantToralRootSubgroupPoints e h ρ M hM hnil b wt j A (Multiplicative.ofAdd 1)⁆ :
          kostantToralPointsSubgroup e h ρ M hM hnil b wt A).property

/-- The underlying matrix is the matrix image of the integral bracket exponential. -/
@[simp]
theorem coe_kostantToralBracketRootSubgroupPoints (A : Type v) [CommRing A]
    (a : Multiplicative A) :
    (kostantToralBracketRootSubgroupPoints e h ρ M hM hnil b wt hi hj A a :
        Matrix.GeneralLinearGroup (Fin n) A) =
      Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom
        (kostantBracketRootSubgroupParam e h ρ M hM hi hj (hnil i) (CommAlgCat.of ℤ A) a) :=
  (rfl)

/-- The class-two Chevalley commutator relation in the matrix-valued toral-closure points. -/
theorem commutatorElement_kostantToralRootSubgroupPoints_eq_bracket
    (A : Type v) [CommRing A] (a c : A) :
    ⁅kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A (Multiplicative.ofAdd a),
        kostantToralRootSubgroupPoints e h ρ M hM hnil b wt j A (Multiplicative.ofAdd c)⁆ =
      kostantToralBracketRootSubgroupPoints e h ρ M hM hnil b wt hi hj A
        (Multiplicative.ofAdd (a * c)) := by
  apply Subtype.ext
  simpa only [coe_kostantToralBracketRootSubgroupPoints] using
    commutator_eq_matrix_bracket e h ρ M hM hnil b wt hi hj A a c

/-- Conjugation by the weight torus rescales the bracket-subgroup parameter by the
character of the sum of the two root weights. -/
theorem kostantToralWeightTorusPoints_conj_bracketRootSubgroupPoints
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    {α β : κ → ℤ} (hα : ∀ k, ⁅h k, e i⁆ = (α k : ℚ) • e i)
    (hβ : ∀ k, ⁅h k, e j⁆ = (β k : ℚ) • e j)
    (A : Type v) [CommRing A] (s : κ → Aˣ) (u : Multiplicative A) :
    kostantToralWeightTorusPoints e h ρ M hM hnil b wt A s *
        kostantToralBracketRootSubgroupPoints e h ρ M hM hnil b wt hi hj A u *
        (kostantToralWeightTorusPoints e h ρ M hM hnil b wt A s)⁻¹ =
      kostantToralBracketRootSubgroupPoints e h ρ M hM hnil b wt hi hj A
        (Multiplicative.ofAdd ((torusCharacter s (α + β) : A) * u.toAdd)) := by
  have hbr := commutatorElement_kostantToralRootSubgroupPoints_eq_bracket
    e h ρ M hM hnil b wt hi hj A u.toAdd 1
  simp only [mul_one, ofAdd_toAdd] at hbr
  rw [← hbr, conjugate_commutatorElement,
    kostantToralWeightTorusPoints_conj_rootSubgroupPoints e h ρ M hM hnil b wt hwt hα,
    kostantToralWeightTorusPoints_conj_rootSubgroupPoints e h ρ M hM hnil b wt hwt hβ,
    commutatorElement_kostantToralRootSubgroupPoints_eq_bracket e h ρ M hM hnil b wt hi hj]
  congr 2
  simp only [torusCharacter_add, Units.val_mul, toAdd_ofAdd, mul_one]
  ring

end TauCeti.UniversalEnvelopingAlgebra
