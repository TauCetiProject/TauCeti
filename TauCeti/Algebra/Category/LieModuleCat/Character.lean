/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.LieModuleCat.Finrank
public import TauCeti.Algebra.Lie.Weights.FormalCharacter

/-!
# The formal character of virtual finite-dimensional Lie modules

Let `L` be a Lie algebra over a field `K`. Finite-dimensional `L`-modules
form the essentially small category `TauCeti.FGLieModuleCat K L` with binary biproducts, so they
have a split Grothendieck group `TauCeti.SplitK0 (FGLieModuleCat K L)`: the group of virtual
finite-dimensional representations `[M] - [N]`, with `[M ⊕ N] = [M] + [N]`.

For a nilpotent Lie subalgebra `H` of `L` (in the main application, a Cartan subalgebra) whose
generalized weights on finite-dimensional modules are linear (as in characteristic zero), the formal
character `TauCeti.formalCharacter K H M` of a finite-dimensional module is an isomorphism
invariant and additive on direct sums. It therefore descends to a homomorphism

`TauCeti.FGLieModuleCat.characterK0 K H : SplitK0 (FGLieModuleCat K L) →+ ℤ[Module.Dual K H]`

sending `[M] - [N]` to `ch M - ch N`. When `H` is triangularizable on every finite-dimensional
module (for instance, when `K` is algebraically closed) the coefficients of the character of a
virtual module add up to its dimension `TauCeti.FGLieModuleCat.finrankK0`. Let `K` have
characteristic zero, `L` be finite-dimensional and Killing, and `H` be a Cartan subalgebra. If `H`
is splitting (`IsTriangularizable K H L`), the character of a virtual module is supported on
integral weights; if `K` is algebraically closed, it is invariant under the Weyl group.

## Main definitions

* `TauCeti.FGLieModuleCat.characterK0`: the formal character of a virtual module.

## Main results

* `TauCeti.FGLieModuleCat.characterK0_splitK0_of`: the value on the class of a module.
* `TauCeti.FGLieModuleCat.sum_characterK0_coeff_eq_finrankK0`: for a triangularizable `H`, the
  augmentation of the character is the dimension `TauCeti.FGLieModuleCat.finrankK0`.
* `TauCeti.FGLieModuleCat.isIntegralWeight_of_characterK0_coeff_ne_zero`: the character of a
  virtual module is supported on integral weights.
* `TauCeti.FGLieModuleCat.characterK0_coeff_weylGroup_smul`: the character of a virtual module is
  Weyl invariant.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Graduate Texts in Mathematics
  129, Lecture 23, for the representation ring of a semisimple Lie algebra and its character
  homomorphism.
-/

public section

open CategoryTheory CategoryTheory.Limits LieAlgebra _root_.LieModule Module

universe w u v

namespace TauCeti.FGLieModuleCat

variable (K : Type u) {L : Type v} [Field K] [LieRing L] [LieAlgebra K L] (H : LieSubalgebra K L)

section Nilpotent

variable [LieRing.IsNilpotent H] [∀ M : FGLieModuleCat.{w} K L, LinearWeights K H M.obj]

/-- The formal character as an invariant of finite-dimensional Lie modules, additive on
biproducts. -/
private noncomputable def characterInvariant :
    SplitK0.AdditiveInvariant (FGLieModuleCat.{w} K L) (AddMonoidAlgebra ℤ (Dual K H)) where
  obj M := formalCharacter K H M.obj
  map_iso _ _ e := formalCharacter_congr (e.fgLieModuleCatIsoToLieModuleEquiv.restrictLie H)
  map_biprod M N := by
    rw [formalCharacter_congr ((biprodLieModuleEquiv M N).restrictLie H), formalCharacter_prod]

/-- **The formal character of a virtual finite-dimensional Lie module**: the homomorphism on the
split Grothendieck group sending `[M] - [N]` to `ch M - ch N`, the characters being read on the
nilpotent Lie subalgebra `H`. -/
noncomputable def characterK0 :
    SplitK0 (FGLieModuleCat.{w} K L) →+ AddMonoidAlgebra ℤ (Dual K H) :=
  SplitK0.lift (characterInvariant K H)

/-- The character of the class of a module is its formal character. -/
@[simp]
theorem characterK0_splitK0_of (M : FGLieModuleCat.{w} K L) :
    characterK0 K H (SplitK0.of M) = formalCharacter K H M.obj :=
  SplitK0.lift_of _ M

/-- **The augmentation of the character is the dimension.** When `H` is triangularizable on every
finite-dimensional module (for instance, over an algebraically closed field), the coefficients of
the character of a virtual module add up to its dimension. -/
theorem sum_characterK0_coeff_eq_finrankK0
    [∀ M : FGLieModuleCat.{w} K L, IsTriangularizable K H M.obj]
    (x : SplitK0 (FGLieModuleCat.{w} K L)) :
    ((characterK0 K H x).coeff.sum fun _ n ↦ n) = finrankK0 K x := by
  induction x using SplitK0.induction_on with
  | zero => simp
  | of M =>
      rw [characterK0_splitK0_of, finrankK0_splitK0_of, sum_formalCharacter_coeff_eq_finrank]
  | add x y hx hy =>
      rw [map_add, map_add, AddMonoidAlgebra.coeff_add,
        Finsupp.sum_add_index' (fun _ ↦ rfl) fun _ _ _ ↦ rfl, hx, hy]
  | neg x hx =>
      rw [map_neg, map_neg, AddMonoidAlgebra.coeff_neg, Finsupp.sum_neg_index fun _ ↦ rfl,
        Finsupp.sum_neg, hx]

end Nilpotent

section Killing

variable {K H} [CharZero K] [IsKilling K L] [FiniteDimensional K L] [H.IsCartanSubalgebra]

/-- **The character of a virtual module is supported on integral weights.** For a splitting Cartan
subalgebra `H` of a finite-dimensional Killing Lie algebra over a field of characteristic zero,
every linear form with a nonzero coefficient in the character of a virtual module is an integral
weight. -/
theorem isIntegralWeight_of_characterK0_coeff_ne_zero [IsTriangularizable K H L]
    {x : SplitK0 (FGLieModuleCat.{w} K L)} {χ : Dual K H} (hχ : (characterK0 K H x).coeff χ ≠ 0) :
    IsIntegralWeight χ := by
  obtain ⟨M, N, rfl⟩ := SplitK0.exists_eq_sub x
  rw [map_sub, characterK0_splitK0_of, characterK0_splitK0_of, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply] at hχ
  by_cases hM : (formalCharacter K H M.obj).coeff χ = 0
  · exact isIntegralWeight_of_formalCharacter_coeff_ne_zero (M := N.obj) fun hN ↦
      hχ (by simp [hM, hN])
  · exact isIntegralWeight_of_formalCharacter_coeff_ne_zero hM

variable [IsAlgClosed K]

/-- **Weyl invariance of the character of a virtual module.** -/
@[simp]
theorem characterK0_coeff_weylGroup_smul (w : (IsKilling.rootSystem H).weylGroup) (χ : Dual K H)
    (x : SplitK0 (FGLieModuleCat.{w} K L)) :
    (characterK0 K H x).coeff (w • χ) = (characterK0 K H x).coeff χ := by
  obtain ⟨M, N, rfl⟩ := SplitK0.exists_eq_sub x
  simp only [map_sub, characterK0_splitK0_of, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    formalCharacter_coeff_weylGroup_smul]

end Killing

end TauCeti.FGLieModuleCat
