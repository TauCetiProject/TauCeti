/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Differential
public import TauCeti.Algebra.Lie.SemiDirect.Basic

/-!
# The Lie algebra of a dynamic parabolic as a semidirect sum

The Lie algebra of a dynamic parabolic is the semidirect sum of its unipotent Lie ideal and
its Levi Lie subalgebra. The action is the restriction of the adjoint action, so the mixed
bracket is retained. The underlying map adds the two ambient tangent derivations, and its
inverse has Levi coordinate equal to the differential of the dynamic limit.

The two factors are realized inside the parabolic Lie algebra: the unipotent ideal is the
kernel of the limit differential, and the Levi subalgebra is the inverse image of the ambient
Levi tangent subalgebra. Their membership lemmas identify these descriptions with vanishing
on the respective defining Hopf ideals. All constructions work over arbitrary commutative
base rings and coefficient algebras, including nonreduced ones.

This combines the differential and tangent decompositions in `Dynamic.LeviDecomposition`
with the internal semidirect-sum recognition theorem `LieIdeal.semiDirectSumEquiv`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10 and 13.
-/

public section

open TauCeti TauCeti.Cocharacter

namespace BialgHom

universe u v

variable {R H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- The tangent Lie ideal of the dynamic unipotent subgroup, inside the parabolic Lie algebra.
It is the kernel of the differential of the dynamic limit. -/
noncomputable def unipotentLieIdeal (l : H →ₐc[R] LaurentPolynomial R) :
    LieIdeal B ((parabolicDefiningHopfIdeal l).lieSubalgebra (B := B)) :=
  (parabolicLimitLieHom (B := B) l).ker

/-- Membership in the unipotent Lie ideal is membership of the ambient tangent vector in
`Lie U(λ)`. -/
@[simp]
theorem mem_unipotentLieIdeal (l : H →ₐc[R] LaurentPolynomial R)
    (d : (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B)) :
    d ∈ unipotentLieIdeal l ↔ d.val ∈ l.unipotentDefiningHopfIdeal.lieSubalgebra := by
  rw [unipotentLieIdeal, LieHom.mem_ker, parabolicLimitLieHom_eq_zero_iff]

/-- The tangent Lie subalgebra of the dynamic Levi, inside the parabolic Lie algebra. -/
noncomputable def leviLieSubalgebra (l : H →ₐc[R] LaurentPolynomial R) :
    LieSubalgebra B ((parabolicDefiningHopfIdeal l).lieSubalgebra (B := B)) :=
  ((leviDefiningHopfIdeal l).lieSubalgebra (B := B)).comap
    ((parabolicDefiningHopfIdeal l).lieSubalgebra (B := B)).incl

/-- Membership in the Levi Lie subalgebra is membership of the ambient tangent vector in
`Lie Z(λ)`. -/
@[simp]
theorem mem_leviLieSubalgebra (l : H →ₐc[R] LaurentPolynomial R)
    (d : (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B)) :
    d ∈ leviLieSubalgebra l ↔ d.val ∈ (leviDefiningHopfIdeal l).lieSubalgebra := by
  rfl

/-- The unipotent ideal and Levi subalgebra are complementary as submodules of `Lie P(λ)`. -/
theorem isCompl_unipotentLieIdeal_leviLieSubalgebra
    (l : H →ₐc[R] LaurentPolynomial R) :
    IsCompl (unipotentLieIdeal (B := B) l).toSubmodule
      (leviLieSubalgebra (B := B) l).toSubmodule := by
  constructor
  · rw [Submodule.disjoint_def]
    intro d hu hz
    apply Subtype.ext
    exact (Submodule.disjoint_def.mp (disjoint_lieSubalgebra_unipotent_levi (B := B) l))
      d.val ((mem_unipotentLieIdeal l d).mp hu) ((mem_leviLieSubalgebra l d).mp hz)
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    intro d
    obtain ⟨u, hu, z, hz, hd⟩ := exists_add_lieSubalgebra_unipotent_levi l d.property
    have hsum := sup_lieSubalgebra_unipotent_levi (B := B) l
    have huP : u ∈ (parabolicDefiningHopfIdeal l).lieSubalgebra := by
      rw [← LieSubalgebra.mem_toSubmodule, ← hsum]
      exact Submodule.mem_sup_left hu
    have hzP : z ∈ (parabolicDefiningHopfIdeal l).lieSubalgebra := by
      rw [← LieSubalgebra.mem_toSubmodule, ← hsum]
      exact Submodule.mem_sup_right hz
    exact ⟨⟨u, huP⟩, ⟨z, hzP⟩, (mem_unipotentLieIdeal l _).mpr hu,
      (mem_leviLieSubalgebra l _).mpr hz, Subtype.ext hd.symm⟩

/-- The Levi Lie algebra acts on the unipotent Lie ideal by the adjoint action. -/
noncomputable def leviLieAction (l : H →ₐc[R] LaurentPolynomial R) :
    leviLieSubalgebra (B := B) l →ₗ⁅B⁆
      LieDerivation B (unipotentLieIdeal (B := B) l) (unipotentLieIdeal (B := B) l) :=
  (LieIdeal.ad (unipotentLieIdeal l)).comp (leviLieSubalgebra l).incl

/-- On ambient derivations the Levi action is the Lie bracket, with the Levi vector first. -/
@[simp]
theorem coe_leviLieAction_apply (l : H →ₐc[R] LaurentPolynomial R)
    (z : leviLieSubalgebra (B := B) l) (u : unipotentLieIdeal (B := B) l) :
    ((leviLieAction l z u).val.val : Derivation R H (Bialgebra.CounitAlgebra R H B)) =
      ⁅z.val.val, u.val.val⁆ := by
  simp only [leviLieAction, LieHom.comp_apply, LieSubalgebra.coe_incl,
    LieIdeal.ad_apply_apply, LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket]

/-- The dynamic Levi decomposition of Lie algebras. The twisting action is the adjoint action
of the Levi on the unipotent ideal, rather than the trivial action of a direct product. -/
noncomputable def leviDecompositionLieEquiv (l : H →ₐc[R] LaurentPolynomial R) :
    ((unipotentLieIdeal (B := B) l) ⋊⁅leviLieAction l⁆ (leviLieSubalgebra (B := B) l)) ≃ₗ⁅B⁆
      (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B) :=
  LieIdeal.semiDirectSumEquiv _ _ (isCompl_unipotentLieIdeal_leviLieSubalgebra l)

/-- The Lie algebra decomposition adds the two vectors in the parabolic Lie algebra. -/
@[simp]
theorem leviDecompositionLieEquiv_apply (l : H →ₐc[R] LaurentPolynomial R)
    (x : (unipotentLieIdeal (B := B) l) ⋊⁅leviLieAction l⁆ (leviLieSubalgebra (B := B) l)) :
    leviDecompositionLieEquiv l x = x.left.val + x.right.val := by
  exact LieIdeal.semiDirectSumEquiv_apply _ _ _ x

/-- The Levi coordinate of the inverse Lie decomposition is the dynamic limit differential,
viewed in the ambient tangent Lie algebra. -/
@[simp]
theorem coe_leviDecompositionLieEquiv_symm_apply_right
    (l : H →ₐc[R] LaurentPolynomial R)
    (d : (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B)) :
    ((leviDecompositionLieEquiv l).symm d).right.val.val = parabolicLimitLieHom l d := by
  let x := (leviDecompositionLieEquiv l).symm d
  have hd : d.val = x.left.val.val + x.right.val.val := by
    have h := congrArg Subtype.val ((leviDecompositionLieEquiv l).apply_symm_apply d)
    rw [leviDecompositionLieEquiv_apply] at h
    exact h.symm
  exact (parabolicLimitLieHom_eq_of_eq_add l d _ _
    ((mem_unipotentLieIdeal l _).mp x.left.property)
    ((mem_leviLieSubalgebra l _).mp x.right.property) hd).symm

/-- The unipotent coordinate of the inverse Lie decomposition subtracts the dynamic limit
differential from the original tangent vector. -/
@[simp]
theorem coe_leviDecompositionLieEquiv_symm_apply_left
    (l : H →ₐc[R] LaurentPolynomial R)
    (d : (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B)) :
    ((leviDecompositionLieEquiv l).symm d).left.val.val = d.val - parabolicLimitLieHom l d := by
  have h := congrArg Subtype.val ((leviDecompositionLieEquiv l).apply_symm_apply d)
  rw [leviDecompositionLieEquiv_apply] at h
  rw [← coe_leviDecompositionLieEquiv_symm_apply_right]
  exact eq_sub_iff_add_eq.mpr h

end BialgHom
