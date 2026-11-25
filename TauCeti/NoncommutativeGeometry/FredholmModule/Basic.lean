/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.SelfAdjoint
public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Operator.Compact.HilbertAdjoint
public import TauCeti.LinearAlgebra.Complex.Module

/-!
# Fredholm modules

A *Fredholm module* over a complex `*`-algebra `A` is a Hilbert space `H` with a
`*`-representation `π : A → B(H)` by bounded operators, which need not be unital, and a
self-adjoint bounded operator `F` such that for every `a : A` the commutator `[F, π(a)]` and the
defect `(F² - 1) π(a)` are compact operators. This is Connes' bounded model of an abstract
elliptic operator over `A`, and the cycle from which the Chern character and the index pairing
with K-theory are built. An *even* Fredholm module also carries a grading `γ`: a self-adjoint
involution commuting with `π` and anticommuting with `F`. A module without grading is called odd.

This file develops the basic operations on Fredholm modules that preserve their class:

* `FredholmModule.ofRealPart`: if an operator `F`, not necessarily self-adjoint, has compact
  commutators `[F, π(a)]` and defects `(F² - 1) π(a)`, and its skew part is compact relative to
  `π` (that is, `(F - F*) π(a)` is compact), then its real part `(F + F*) / 2` is the operator of
  a Fredholm module.
* `FredholmModule.perturb`: replacing `F` by `F + K` for a self-adjoint `K` with `K π(a)`
  compact for every `a`. In particular every compact self-adjoint perturbation is allowed.
* `FredholmModule.conj`: transport along a unitary `U : H ≃ H'`, giving unitarily equivalent
  modules.
* `FredholmModule.ofFiniteDimensional`: on a finite-dimensional Hilbert space every
  `*`-representation with every self-adjoint operator is a Fredholm module.
* `FredholmModule.IsNormalized`, `FredholmModule.IsDegenerate`, `FredholmModule.zeroRep`:
  involutive (`F² = 1`) and degenerate (`[F, π(a)] = 0`, `(F² - 1) π(a) = 0`) predicates and
  zero-representation degenerate modules.
* `EvenFredholmModule.flipGrading`: orientation reversal `γ ↦ -γ` of an even Fredholm module.

Each construction has its even counterpart in the `EvenFredholmModule` namespace.

The defining conditions are one-sided, but the compact operators form a two-sided `*`-ideal and
`π` is a `*`-homomorphism, so they imply their mirror images:
`FredholmModule.isCompactOperator_rep_mul_mul_self_sub_one` shows that `π(a) (F² - 1)` is compact.

## Main definitions

* `TauCeti.FredholmModule A H`: an odd Fredholm module over `A` on `H`.
* `TauCeti.EvenFredholmModule A H`: an even Fredholm module, with grading `γ`.
* `TauCeti.FredholmModule.IsNormalized`, `TauCeti.FredholmModule.IsDegenerate`: normalized and
  degenerate predicates (with `EvenFredholmModule` counterparts).
* `TauCeti.FredholmModule.zeroRep`, `TauCeti.EvenFredholmModule.zeroRep`: zero-representation
  degenerate modules.
* `TauCeti.EvenFredholmModule.flipGrading`: grading sign reversal `γ ↦ -γ`.

## References

* A. Connes, *Noncommutative Geometry*, Academic Press (1994), Chapter IV, §1.
* N. Higson, J. Roe, *Analytic K-Homology*, Oxford Mathematical Monographs (2000), Chapter 8.
-/

public section

noncomputable section

open scoped ComplexStarModule

namespace TauCeti

variable (A : Type*) [NonUnitalNonAssocSemiring A] [Module ℂ A] [Star A]
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section CompleteSpace

variable [CompleteSpace H]

/-- An odd **Fredholm module** over the complex `*`-algebra `A` on the Hilbert space `H`: a
`*`-representation `rep` of `A` by bounded operators, which need not be unital, and a
self-adjoint bounded operator `operator` (Connes' `F`) such that `[F, π(a)]` and `(F² - 1) π(a)`
are compact for every `a`. -/
@[ext]
structure FredholmModule where
  /-- The representation `π` of `A` by bounded operators on `H`; it need not be unital. -/
  rep : A →⋆ₙₐ[ℂ] H →L[ℂ] H
  /-- The operator `F` of the Fredholm module. -/
  operator : H →L[ℂ] H
  isSelfAdjoint_operator : IsSelfAdjoint operator
  isCompactOperator_commutator (a : A) : IsCompactOperator ⇑(operator * rep a - rep a * operator)
  isCompactOperator_mul_self_sub_one_mul (a : A) :
    IsCompactOperator ⇑((operator * operator - 1) * rep a)

/-- An **even Fredholm module** over `A` on `H`: a Fredholm module together with a grading
`γ`, a self-adjoint involution of `H` that commutes with the representation and anticommutes
with the operator `F`. -/
@[ext]
structure EvenFredholmModule extends FredholmModule A H where
  /-- The grading operator `γ`. -/
  grading : H →L[ℂ] H
  isSelfAdjoint_grading : IsSelfAdjoint grading
  grading_mul_grading : grading * grading = 1
  commute_grading_rep (a : A) : Commute grading (rep a)
  grading_mul_operator : grading * operator = -(operator * grading)

end CompleteSpace

variable {A H}

/-! ### Odd Fredholm modules -/

namespace FredholmModule

section CompleteSpace

variable [CompleteSpace H] (M : FredholmModule A H)

/-- The operator of a Fredholm module equals its adjoint. -/
@[simp]
theorem star_operator : star M.operator = M.operator :=
  M.isSelfAdjoint_operator.star_eq

/-- **Mirror image of the defect condition.** `π(a) (F² - 1)` is compact for every `a`. -/
theorem isCompactOperator_rep_mul_mul_self_sub_one (a : A) :
    IsCompactOperator ⇑(M.rep a * (M.operator * M.operator - 1)) := by
  simpa only [star_mul, map_star, star_star, star_sub, star_one, M.star_operator] using
    (M.isCompactOperator_mul_self_sub_one_mul (star a)).star

/-- **Self-adjoint replacement.** Let `F` be a bounded operator whose skew part is compact
relative to `π`, i.e. `(F - F*) π(a)` is compact for every `a`. If `[F, π(a)]` and
`(F² - 1) π(a)` are compact for every `a`, then the real part `ℜ F = (F + F*) / 2` is the operator
of a Fredholm module with representation `π`. -/
def ofRealPart (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H) (F : H →L[ℂ] H)
    (hc : ∀ a, IsCompactOperator ⇑(F * π a - π a * F))
    (hs : ∀ a, IsCompactOperator ⇑((F * F - 1) * π a))
    (hskew : ∀ a, IsCompactOperator ⇑((F - star F) * π a)) : FredholmModule A H where
  rep := π
  operator := ℜ F
  isSelfAdjoint_operator := (ℜ F).property
  isCompactOperator_commutator a := by
    rw [realPart_eq_add_half_star_sub]
    refine ContinuousLinearMap.isCompactOperator_add_commutator (hc a) ?_ ?_
    · rw [smul_mul_assoc, ← neg_sub, neg_mul]
      exact (hskew a).neg.smul _
    · have h : IsCompactOperator ⇑(π a * (star F - F)) := by
        simpa only [star_mul, map_star, star_star, star_sub] using (hskew (star a)).star
      rw [mul_smul_comm, FunLike.coe_smul]
      exact h.smul _
  isCompactOperator_mul_self_sub_one_mul a := by
    rw [realPart_eq_add_half_star_sub]
    refine ContinuousLinearMap.isCompactOperator_add_mul_self_sub_one_mul (hc a) (hs a) ?_
    rw [smul_mul_assoc, ← neg_sub, neg_mul]
    exact (hskew a).neg.smul _

@[simp]
theorem ofRealPart_rep (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H) (F : H →L[ℂ] H) (hc hs hskew) :
    (ofRealPart π F hc hs hskew).rep = π :=
  (rfl)

@[simp]
theorem ofRealPart_operator (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H) (F : H →L[ℂ] H) (hc hs hskew) :
    (ofRealPart π F hc hs hskew).operator = ℜ F :=
  (rfl)

/-- **Relatively compact perturbation.** Replacing the operator `F` of a Fredholm module by
`F + K`, for a self-adjoint `K` with `K π(a)` compact for every `a`, gives a Fredholm module with
the same representation. -/
def perturb (K : H →L[ℂ] H) (hK : IsSelfAdjoint K)
    (hKc : ∀ a, IsCompactOperator ⇑(K * M.rep a)) : FredholmModule A H where
  rep := M.rep
  operator := M.operator + K
  isSelfAdjoint_operator := M.isSelfAdjoint_operator.add hK
  isCompactOperator_commutator a :=
    ContinuousLinearMap.isCompactOperator_add_commutator (M.isCompactOperator_commutator a)
      (hKc a) (by simpa only [star_mul, map_star, star_star, hK.star_eq] using (hKc (star a)).star)
  isCompactOperator_mul_self_sub_one_mul a :=
    ContinuousLinearMap.isCompactOperator_add_mul_self_sub_one_mul
      (M.isCompactOperator_commutator a) (M.isCompactOperator_mul_self_sub_one_mul a) (hKc a)

@[simp]
theorem perturb_rep (K : H →L[ℂ] H) (hK hKc) : (M.perturb K hK hKc).rep = M.rep :=
  (rfl)

@[simp]
theorem perturb_operator (K : H →L[ℂ] H) (hK hKc) :
    (M.perturb K hK hKc).operator = M.operator + K :=
  (rfl)

section Conj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- **Unitary equivalence.** The Fredholm module on `H'` obtained by transporting `M` along the
unitary `U : H ≃ H'`, with representation `U π(a) U*` and operator `U F U*`. -/
def conj (U : H ≃ₗᵢ[ℂ] H') : FredholmModule A H' where
  rep := (NonUnitalStarAlgHom.ofClass U.conjStarAlgEquiv).comp M.rep
  operator := U.conjStarAlgEquiv M.operator
  isSelfAdjoint_operator := M.isSelfAdjoint_operator.map U.conjStarAlgEquiv
  isCompactOperator_commutator a := by
    simpa only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_ofClass, ← map_mul,
      ← map_sub] using (M.isCompactOperator_commutator a).conjStarAlgEquiv U
  isCompactOperator_mul_self_sub_one_mul a := by
    simpa only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_ofClass, ← map_mul,
      ← map_sub, ← map_one U.conjStarAlgEquiv] using
      (M.isCompactOperator_mul_self_sub_one_mul a).conjStarAlgEquiv U

@[simp]
theorem conj_rep_apply (U : H ≃ₗᵢ[ℂ] H') (a : A) :
    (M.conj U).rep a = U.conjStarAlgEquiv (M.rep a) :=
  (rfl)

@[simp]
theorem conj_operator (U : H ≃ₗᵢ[ℂ] H') : (M.conj U).operator = U.conjStarAlgEquiv M.operator :=
  (rfl)

/-- Transporting back along the inverse unitary recovers the original module. -/
@[simp]
theorem conj_conj_symm (U : H ≃ₗᵢ[ℂ] H') : (M.conj U).conj U.symm = M := by
  ext1
  · ext1 a
    simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]
  · simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]

/-- Transporting along the inverse unitary and then along `U` recovers the original module. -/
@[simp]
theorem conj_symm_conj (U : H' ≃ₗᵢ[ℂ] H) : (M.conj U.symm).conj U = M := by
  simpa using (M.conj_conj_symm U.symm)

/-- Transporting along the identity unitary does nothing. -/
@[simp]
theorem conj_refl : M.conj (LinearIsometryEquiv.refl ℂ H) = M := by
  ext1
  · ext1 a
    simp
  · simp

/-- Transporting along `U` and then along `V` is transporting along their composite. -/
theorem conj_trans {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
    [CompleteSpace H''] (U : H ≃ₗᵢ[ℂ] H') (V : H' ≃ₗᵢ[ℂ] H'') :
    (M.conj U).conj V = M.conj (U.trans V) :=
  (rfl)

end Conj

end CompleteSpace

section PredicatesAndZeroRep

variable [CompleteSpace H]

/-- A Fredholm module is **normalized** (or involutive) when `F² = 1`. -/
def IsNormalized (M : FredholmModule A H) : Prop :=
  M.operator * M.operator = 1

/-- Characterization of normalized Fredholm modules by `F² = 1` (not `@[simp]`, so conditional
`@[simp]` lemmas taking `hM : M.IsNormalized` remain in `simp` normal form). -/
theorem isNormalized_iff {M : FredholmModule A H} :
    M.IsNormalized ↔ M.operator * M.operator = 1 :=
  (Iff.rfl)

@[simp]
theorem IsNormalized.operator_mul_operator {M : FredholmModule A H} (hM : M.IsNormalized) :
    M.operator * M.operator = 1 :=
  hM

theorem IsNormalized.isCompactOperator_mul_self_sub_one {M : FredholmModule A H}
    (hM : M.IsNormalized) : IsCompactOperator ⇑(M.operator * M.operator - 1) := by
  rw [hM.operator_mul_operator, sub_self]
  exact isCompactOperator_zero

/-- A Fredholm module is **degenerate** when `[F, π(a)] = 0` and `(F² - 1) π(a) = 0` for every
`a : A`. -/
structure IsDegenerate (M : FredholmModule A H) : Prop where
  commutator_eq_zero (a : A) : M.operator * M.rep a - M.rep a * M.operator = 0
  mul_self_sub_one_mul_eq_zero (a : A) : (M.operator * M.operator - 1) * M.rep a = 0

theorem IsDegenerate.commute_operator_rep {M : FredholmModule A H} (hM : M.IsDegenerate) (a : A) :
    Commute M.operator (M.rep a) :=
  sub_eq_zero.mp (hM.commutator_eq_zero a)

theorem IsDegenerate.rep_mul_mul_self_sub_one_eq_zero {M : FredholmModule A H}
    (hM : M.IsDegenerate) (a : A) :
    M.rep a * (M.operator * M.operator - 1) = 0 := by
  have h := congrArg star (hM.mul_self_sub_one_mul_eq_zero (star a))
  rwa [star_mul, map_star, star_star, star_sub, star_mul, star_one, M.star_operator,
    star_zero] at h

section ConjPredicates

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

theorem IsNormalized.conj {M : FredholmModule A H} (hM : M.IsNormalized) (U : H ≃ₗᵢ[ℂ] H') :
    (M.conj U).IsNormalized := by
  rw [IsNormalized, conj_operator, ← map_mul, hM.operator_mul_operator, map_one]

theorem IsDegenerate.conj {M : FredholmModule A H} (hM : M.IsDegenerate) (U : H ≃ₗᵢ[ℂ] H') :
    (M.conj U).IsDegenerate where
  commutator_eq_zero a := by
    rw [conj_operator, conj_rep_apply, ← map_mul, ← map_mul, ← map_sub,
      hM.commutator_eq_zero a, map_zero]
  mul_self_sub_one_mul_eq_zero a := by
    rw [conj_operator, conj_rep_apply, ← map_mul, ← map_one U.conjStarAlgEquiv, ← map_sub,
      ← map_mul, hM.mul_self_sub_one_mul_eq_zero a, map_zero]

end ConjPredicates

variable (A) in
/-- The degenerate Fredholm module with zero representation `π = 0` and a given self-adjoint
operator `F`. -/
def zeroRep (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) : FredholmModule A H where
  rep :=
    { (0 : A →ₙₐ[ℂ] H →L[ℂ] H) with
      map_star' _ := by simp }
  operator := F
  isSelfAdjoint_operator := hF
  isCompactOperator_commutator _ := by simp [isCompactOperator_zero]
  isCompactOperator_mul_self_sub_one_mul _ := by simp [isCompactOperator_zero]

@[simp]
theorem zeroRep_rep_apply (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) (a : A) :
    (zeroRep A F hF).rep a = 0 :=
  (rfl)

@[simp]
theorem zeroRep_operator (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) : (zeroRep A F hF).operator = F :=
  (rfl)

theorem isDegenerate_zeroRep (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) :
    (zeroRep A F hF).IsDegenerate where
  commutator_eq_zero _ := by simp
  mul_self_sub_one_mul_eq_zero _ := by simp

end PredicatesAndZeroRep

section FiniteDimensional

variable [FiniteDimensional ℂ H]

/-- On a finite-dimensional Hilbert space every operator is compact, so every
`*`-representation together with every self-adjoint operator is a Fredholm module. -/
def ofFiniteDimensional (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H) (F : H →L[ℂ] H)
    (hF : IsSelfAdjoint F) : FredholmModule A H where
  rep := π
  operator := F
  isSelfAdjoint_operator := hF
  isCompactOperator_commutator _ := isCompactOperator_of_locallyCompactSpace_dom _
  isCompactOperator_mul_self_sub_one_mul _ := isCompactOperator_of_locallyCompactSpace_dom _

@[simp]
theorem ofFiniteDimensional_rep (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H)
    (F : H →L[ℂ] H) (hF) : (ofFiniteDimensional π F hF).rep = π :=
  (rfl)

@[simp]
theorem ofFiniteDimensional_operator (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H)
    (F : H →L[ℂ] H) (hF) : (ofFiniteDimensional π F hF).operator = F :=
  (rfl)

end FiniteDimensional

end FredholmModule

/-! ### Even Fredholm modules -/

namespace EvenFredholmModule

section CompleteSpace

variable [CompleteSpace H] (M : EvenFredholmModule A H)

/-- The grading of an even Fredholm module equals its adjoint. -/
@[simp]
theorem star_grading : star M.grading = M.grading :=
  M.isSelfAdjoint_grading.star_eq

/-- **Self-adjoint replacement**, even version: if `γ` anticommutes with `F`, it anticommutes
with the real part `ℜ F` used by `FredholmModule.ofRealPart`. -/
def ofRealPart (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H) (F : H →L[ℂ] H)
    (hc : ∀ a, IsCompactOperator ⇑(F * π a - π a * F))
    (hs : ∀ a, IsCompactOperator ⇑((F * F - 1) * π a))
    (hskew : ∀ a, IsCompactOperator ⇑((F - star F) * π a)) (γ : H →L[ℂ] H)
    (hγ : IsSelfAdjoint γ) (hγγ : γ * γ = 1) (hγπ : ∀ a, Commute γ (π a))
    (hγF : γ * F = -(F * γ)) : EvenFredholmModule A H where
  toFredholmModule := FredholmModule.ofRealPart π F hc hs hskew
  grading := γ
  isSelfAdjoint_grading := hγ
  grading_mul_grading := hγγ
  commute_grading_rep := hγπ
  grading_mul_operator := by
    simp [realPart_apply_coe, mul_add, add_mul, hγF, hγ.mul_star_eq_neg_star_mul hγF, add_comm]

@[simp]
theorem ofRealPart_toFredholmModule (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H) (F : H →L[ℂ] H)
    (hc hs hskew) (γ : H →L[ℂ] H) (hγ hγγ hγπ hγF) :
    (ofRealPart π F hc hs hskew γ hγ hγγ hγπ hγF).toFredholmModule =
      FredholmModule.ofRealPart π F hc hs hskew :=
  (rfl)

@[simp]
theorem ofRealPart_grading (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H) (F : H →L[ℂ] H)
    (hc hs hskew) (γ : H →L[ℂ] H) (hγ hγγ hγπ hγF) :
    (ofRealPart π F hc hs hskew γ hγ hγγ hγπ hγF).grading = γ :=
  (rfl)

/-- **Relatively compact perturbation**, even version: the perturbing operator `K` must
anticommute with the grading. -/
def perturb (K : H →L[ℂ] H) (hK : IsSelfAdjoint K)
    (hKc : ∀ a, IsCompactOperator ⇑(K * M.rep a)) (hγK : M.grading * K = -(K * M.grading)) :
    EvenFredholmModule A H where
  toFredholmModule := M.toFredholmModule.perturb K hK hKc
  grading := M.grading
  isSelfAdjoint_grading := M.isSelfAdjoint_grading
  grading_mul_grading := M.grading_mul_grading
  commute_grading_rep := M.commute_grading_rep
  grading_mul_operator := by
    rw [FredholmModule.perturb_operator, mul_add, add_mul, M.grading_mul_operator, hγK, neg_add]

@[simp]
theorem perturb_toFredholmModule (K : H →L[ℂ] H) (hK hKc hγK) :
    (M.perturb K hK hKc hγK).toFredholmModule = M.toFredholmModule.perturb K hK hKc :=
  (rfl)

@[simp]
theorem perturb_grading (K : H →L[ℂ] H) (hK hKc hγK) :
    (M.perturb K hK hKc hγK).grading = M.grading :=
  (rfl)

section Conj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- **Unitary equivalence**, even version: the grading is transported to `U γ U*`. -/
def conj (U : H ≃ₗᵢ[ℂ] H') : EvenFredholmModule A H' where
  toFredholmModule := M.toFredholmModule.conj U
  grading := U.conjStarAlgEquiv M.grading
  isSelfAdjoint_grading := M.isSelfAdjoint_grading.map U.conjStarAlgEquiv
  grading_mul_grading := by rw [← map_mul, M.grading_mul_grading, map_one]
  commute_grading_rep a := by
    rw [FredholmModule.conj_rep_apply]
    exact (M.commute_grading_rep a).map U.conjStarAlgEquiv
  grading_mul_operator := by
    rw [FredholmModule.conj_operator, ← map_mul, M.grading_mul_operator, map_neg, map_mul]

@[simp]
theorem conj_toFredholmModule (U : H ≃ₗᵢ[ℂ] H') :
    (M.conj U).toFredholmModule = M.toFredholmModule.conj U :=
  (rfl)

@[simp]
theorem conj_grading (U : H ≃ₗᵢ[ℂ] H') : (M.conj U).grading = U.conjStarAlgEquiv M.grading :=
  (rfl)

/-- Transporting back along the inverse unitary recovers the original module. -/
@[simp]
theorem conj_conj_symm (U : H ≃ₗᵢ[ℂ] H') : (M.conj U).conj U.symm = M := by
  ext1
  · simp
  · simp
  · simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]

/-- Transporting along the inverse unitary and then along `U` recovers the original module. -/
@[simp]
theorem conj_symm_conj (U : H' ≃ₗᵢ[ℂ] H) : (M.conj U.symm).conj U = M := by
  simpa using (M.conj_conj_symm U.symm)

/-- Transporting along the identity unitary does nothing. -/
@[simp]
theorem conj_refl : M.conj (LinearIsometryEquiv.refl ℂ H) = M := by
  ext1
  · simp
  · simp
  · simp

/-- Transporting along `U` and then along `V` is transporting along their composite. -/
theorem conj_trans {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
    [CompleteSpace H''] (U : H ≃ₗᵢ[ℂ] H') (V : H' ≃ₗᵢ[ℂ] H'') :
    (M.conj U).conj V = M.conj (U.trans V) :=
  (rfl)

end Conj

/-- Reversing the sign of the grading `γ ↦ -γ` reverses the orientation of an even Fredholm
module. -/
def flipGrading : EvenFredholmModule A H where
  toFredholmModule := M.toFredholmModule
  grading := -M.grading
  isSelfAdjoint_grading := M.isSelfAdjoint_grading.neg
  grading_mul_grading := by rw [neg_mul_neg, M.grading_mul_grading]
  commute_grading_rep a := (M.commute_grading_rep a).neg_left
  grading_mul_operator := by rw [neg_mul, mul_neg, M.grading_mul_operator]

@[simp]
theorem flipGrading_toFredholmModule : M.flipGrading.toFredholmModule = M.toFredholmModule :=
  (rfl)

@[simp]
theorem flipGrading_grading : M.flipGrading.grading = -M.grading :=
  (rfl)

@[simp]
theorem flipGrading_flipGrading : M.flipGrading.flipGrading = M := by
  ext1 <;> simp

end CompleteSpace

section PredicatesAndZeroRep

variable [CompleteSpace H]

/-- An even Fredholm module is **normalized** when its underlying operator satisfies `F² = 1`. -/
abbrev IsNormalized (M : EvenFredholmModule A H) : Prop :=
  M.toFredholmModule.IsNormalized

theorem isNormalized_iff {M : EvenFredholmModule A H} :
    M.IsNormalized ↔ M.operator * M.operator = 1 :=
  (Iff.rfl)

/-- An even Fredholm module is **degenerate** when `[F, π(a)] = 0` and `(F² - 1) π(a) = 0` for
every `a : A`. -/
abbrev IsDegenerate (M : EvenFredholmModule A H) : Prop :=
  M.toFredholmModule.IsDegenerate

variable (A) in
/-- The degenerate even Fredholm module with zero representation `π = 0`, operator `F`, and
grading `γ` anticommuting with `F`. -/
def zeroRep (F γ : H →L[ℂ] H) (hF : IsSelfAdjoint F) (hγ : IsSelfAdjoint γ) (hγγ : γ * γ = 1)
    (hγF : γ * F = -(F * γ)) : EvenFredholmModule A H where
  toFredholmModule := FredholmModule.zeroRep A F hF
  grading := γ
  isSelfAdjoint_grading := hγ
  grading_mul_grading := hγγ
  commute_grading_rep _ := Commute.zero_right γ
  grading_mul_operator := hγF

@[simp]
theorem zeroRep_toFredholmModule (F γ : H →L[ℂ] H) (hF hγ hγγ hγF) :
    (zeroRep A F γ hF hγ hγγ hγF).toFredholmModule = FredholmModule.zeroRep A F hF :=
  (rfl)

@[simp]
theorem zeroRep_grading (F γ : H →L[ℂ] H) (hF hγ hγγ hγF) :
    (zeroRep A F γ hF hγ hγγ hγF).grading = γ :=
  (rfl)

theorem isDegenerate_zeroRep (F γ : H →L[ℂ] H) (hF hγ hγγ hγF) :
    (zeroRep A F γ hF hγ hγγ hγF).IsDegenerate :=
  FredholmModule.isDegenerate_zeroRep F hF

end PredicatesAndZeroRep

section FiniteDimensional

variable [FiniteDimensional ℂ H]

/-- On a finite-dimensional Hilbert space, every `*`-representation, self-adjoint operator `F` and
grading `γ` commuting with the representation and anticommuting with `F` form an even Fredholm
module. -/
def ofFiniteDimensional (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H) (F : H →L[ℂ] H)
    (hF : IsSelfAdjoint F) (γ : H →L[ℂ] H) (hγ : IsSelfAdjoint γ) (hγγ : γ * γ = 1)
    (hγπ : ∀ a, Commute γ (π a)) (hγF : γ * F = -(F * γ)) : EvenFredholmModule A H where
  toFredholmModule := FredholmModule.ofFiniteDimensional π F hF
  grading := γ
  isSelfAdjoint_grading := hγ
  grading_mul_grading := hγγ
  commute_grading_rep := hγπ
  grading_mul_operator := hγF

@[simp]
theorem ofFiniteDimensional_toFredholmModule (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H)
    (F : H →L[ℂ] H) (hF) (γ : H →L[ℂ] H) (hγ hγγ hγπ hγF) :
    (ofFiniteDimensional π F hF γ hγ hγγ hγπ hγF).toFredholmModule =
      FredholmModule.ofFiniteDimensional π F hF :=
  (rfl)

@[simp]
theorem ofFiniteDimensional_grading (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H)
    (F : H →L[ℂ] H) (hF) (γ : H →L[ℂ] H) (hγ hγγ hγπ hγF) :
    (ofFiniteDimensional π F hF γ hγ hγγ hγπ hγF).grading = γ :=
  (rfl)

end FiniteDimensional

end EvenFredholmModule

end TauCeti
