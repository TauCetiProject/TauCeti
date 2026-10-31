/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
public import TauCeti.Analysis.Normed.Algebra.SeparatingIdeal.Semisimple

/-!
# Uniqueness of the complete norm on a semisimple Banach algebra

Johnson's uniqueness-of-norm theorem: a complex algebra with zero Jacobson radical carries at
most one complete algebra norm up to equivalence. If `f` and `g` are submultiplicative norms on
`A` with `f (c • x) ≤ ‖c‖ * f x` for scalars `c` (and so `ℂ`-homogeneous), under which `A` is
complete, then there are positive constants with `f x ≤ C₁ * g x` and `g x ≤ C₂ * f x` for every
`x`. The algebra `A` need not be unital, and semisimplicity is the purely algebraic condition that
the Jacobson radical of `A`, defined through its unitization when `A` has no unit, is zero.

The two norms are placed on two copies of `A`, which are complex Banach algebras. The identity
map between the copies is a surjective algebra homomorphism onto a semisimple Banach algebra, so
it is continuous by Johnson's automatic-continuity theorem. Applying this in both directions
gives the two norm bounds.

The norm-indexed copy of `A` follows the construction of `AlgebraNorm.copy` in Mathlib's
`Mathlib.Analysis.Normed.Unbundled.IsPowMulUnique`, where a norm is placed on a type synonym and
the identity map between two such copies is bounded to compare the norms.

## Main results

* `RingNorm.exists_le_mul_and_le_mul_of_nonUnitalJacobson_eq_bot`: two complete
  scalar-compatible ring norms on a possibly nonunital semisimple complex algebra are equivalent.
* `AlgebraNorm.exists_le_mul_and_le_mul_of_jacobson_eq_bot`: two complete algebra norms on a
  unital semisimple complex algebra are equivalent.

## References

* B. E. Johnson, *The uniqueness of the (complete) norm topology*, Bull. Amer. Math. Soc. 73
  (1967), 537–539.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §5.2.
-/

noncomputable section

namespace RingNorm

variable {A : Type*} [NonUnitalRing A] [Module ℂ A]

/-- A copy of `A` whose norm is the ring norm `N`, compatible with scalars by `_hN`. -/
def Copy (N : RingNorm A) (_hN : ∀ (c : ℂ) (x : A), N (c • x) ≤ ‖c‖ * N x) : Type _ := A

variable (N : RingNorm A) (hN : ∀ (c : ℂ) (x : A), N (c • x) ≤ ‖c‖ * N x)

instance : NonUnitalRing (N.Copy hN) := inferInstanceAs (NonUnitalRing A)

instance : Module ℂ (N.Copy hN) := inferInstanceAs (Module ℂ A)

instance : NonUnitalNormedRing (N.Copy hN) where
  __ := (inferInstance : NonUnitalRing (N.Copy hN))
  __ := N.toAddGroupNorm.toNormedAddCommGroup
  norm_mul_le := map_mul_le_mul N

instance : NormedSpace ℂ (N.Copy hN) where
  __ := (inferInstance : Module ℂ (N.Copy hN))
  norm_smul_le := hN

instance [IsScalarTower ℂ A A] : IsScalarTower ℂ (N.Copy hN) (N.Copy hN) :=
  inferInstanceAs (IsScalarTower ℂ A A)

instance [SMulCommClass ℂ A A] : SMulCommClass ℂ (N.Copy hN) (N.Copy hN) :=
  inferInstanceAs (SMulCommClass ℂ A A)

end RingNorm

public section

namespace RingNorm

variable {A : Type*} [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

/-- **Johnson's uniqueness-of-norm theorem.** On a complex algebra `A` with zero Jacobson radical,
not necessarily unital, any two ring norms compatible with scalars, under which `A` is complete,
are equivalent. -/
theorem exists_le_mul_and_le_mul_of_nonUnitalJacobson_eq_bot (f g : RingNorm A)
    (hfs : ∀ (c : ℂ) (x : A), f (c • x) ≤ ‖c‖ * f x)
    (hgs : ∀ (c : ℂ) (x : A), g (c • x) ≤ ‖c‖ * g x)
    (hf : letI := f.toAddGroupNorm.toNormedAddCommGroup; CompleteSpace A)
    (hg : letI := g.toAddGroupNorm.toNormedAddCommGroup; CompleteSpace A)
    (hA : TauCeti.nonUnitalJacobson ℂ A = ⊥) :
    ∃ (C₁ C₂ : ℝ) (_ : 0 < C₁) (_ : 0 < C₂), ∀ x : A, f x ≤ C₁ * g x ∧ g x ≤ C₂ * f x := by
  -- The copies `f.Copy hfs` and `g.Copy hgs` have the same algebra structure as `A`, so `hA`, `hf`
  -- and `hg` transfer to them, and the identity of `A` is an algebra homomorphism between them.
  have : CompleteSpace (f.Copy hfs) := hf
  have : CompleteSpace (g.Copy hgs) := hg
  let θ : g.Copy hgs →ₙₐ[ℂ] f.Copy hfs := NonUnitalAlgHom.id ℂ A
  let η : f.Copy hfs →ₙₐ[ℂ] g.Copy hgs := NonUnitalAlgHom.id ℂ A
  let T : g.Copy hgs →L[ℂ] f.Copy hfs :=
    ⟨θ, θ.continuous_of_surjective_of_nonUnitalJacobson_eq_bot Function.surjective_id hA⟩
  let S : f.Copy hfs →L[ℂ] g.Copy hgs :=
    ⟨η, η.continuous_of_surjective_of_nonUnitalJacobson_eq_bot Function.surjective_id hA⟩
  obtain ⟨C₁, hC₁, h₁⟩ := T.bound
  obtain ⟨C₂, hC₂, h₂⟩ := S.bound
  exact ⟨C₁, C₂, hC₁, hC₂, fun x ↦ ⟨h₁ x, h₂ x⟩⟩

end RingNorm

namespace AlgebraNorm

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **Johnson's uniqueness-of-norm theorem.** On a unital complex algebra `A` with zero Jacobson
radical, any two algebra norms under which `A` is complete are equivalent. -/
theorem exists_le_mul_and_le_mul_of_jacobson_eq_bot (f g : AlgebraNorm ℂ A)
    (hf : letI := f.toAddGroupNorm.toNormedAddCommGroup; CompleteSpace A)
    (hg : letI := g.toAddGroupNorm.toNormedAddCommGroup; CompleteSpace A)
    (hA : Ring.jacobson A = ⊥) :
    ∃ (C₁ C₂ : ℝ) (_ : 0 < C₁) (_ : 0 < C₂), ∀ x : A, f x ≤ C₁ * g x ∧ g x ≤ C₂ * f x := by
  refine f.toRingNorm.exists_le_mul_and_le_mul_of_nonUnitalJacobson_eq_bot g.toRingNorm
    (fun c x ↦ (map_smul_eq_mul f c x).le) (fun c x ↦ (map_smul_eq_mul g c x).le) hf hg ?_
  ext a
  simp [TauCeti.nonUnitalJacobson_eq_toTwoSided_jacobson, hA]

end AlgebraNorm
