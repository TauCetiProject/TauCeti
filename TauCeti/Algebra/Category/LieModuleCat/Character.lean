/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.LieModuleCat.EssentiallySmall
public import TauCeti.Algebra.Lie.Weights.FormalCharacter
public import TauCeti.CategoryTheory.GrothendieckGroup.Split

/-!
# The formal character of virtual finite-dimensional Lie modules

Let `L` be a Lie algebra over a field `K` of characteristic zero. Finite-dimensional `L`-modules
form the essentially small category `TauCeti.FGLieModuleCat K L` with binary biproducts, so they
have a split Grothendieck group `TauCeti.SplitK0 (FGLieModuleCat K L)`: the group of virtual
finite-dimensional representations `[M] - [N]`, with `[M ⊕ N] = [M] + [N]`.

For a nilpotent Lie subalgebra `H` of `L` (in the main application, a Cartan subalgebra), the formal
character `TauCeti.formalCharacter K H M` of a finite-dimensional module is an isomorphism
invariant and additive on direct sums. It therefore descends to a homomorphism

`TauCeti.FGLieModuleCat.character K H : SplitK0 (FGLieModuleCat K L) →+ ℤ[Module.Dual K H]`

sending `[M] - [N]` to `ch M - ch N`; likewise dimension descends to
`TauCeti.FGLieModuleCat.dimension`. When `K` is algebraically closed the coefficients of the
character of a virtual module add up to its dimension, and for a Cartan subalgebra of a
Killing-semisimple Lie algebra the character of a virtual module is supported on integral weights
and invariant under the Weyl group.

## Main definitions

* `TauCeti.FGLieModuleCat.character`: the formal character of a virtual module.
* `TauCeti.FGLieModuleCat.dimension`: the dimension of a virtual module.

## Main results

* `TauCeti.FGLieModuleCat.character_of`, `TauCeti.FGLieModuleCat.dimension_of`: the values on the
  class of a module.
* `TauCeti.FGLieModuleCat.sum_character_coeff_eq_dimension`: over an algebraically closed field,
  the augmentation of the character is the dimension.
* `TauCeti.FGLieModuleCat.isIntegralWeight_of_character_coeff_ne_zero`: the character of a virtual
  module is supported on integral weights.
* `TauCeti.FGLieModuleCat.character_coeff_weylGroup_smul`: the character of a virtual module is
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

variable (K : Type u) {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]

/-! ### Dimension -/

/-- Dimension as an invariant of finite-dimensional Lie modules, additive on biproducts. -/
private noncomputable def dimensionInvariant :
    SplitK0.AdditiveInvariant (FGLieModuleCat.{w} K L) ℤ where
  obj M := finrank K M.obj
  map_iso _ _ e := congrArg Nat.cast (isoToLieModuleEquiv e).toLinearEquiv.finrank_eq
  map_biprod M N := by
    rw [(biprodLieModuleEquiv M N).toLinearEquiv.finrank_eq, finrank_prod, Nat.cast_add]

/-- **The dimension of a virtual finite-dimensional Lie module**: the homomorphism on the split
Grothendieck group sending `[M] - [N]` to `dim M - dim N`. -/
noncomputable def dimension : SplitK0 (FGLieModuleCat.{w} K L) →+ ℤ :=
  SplitK0.lift (dimensionInvariant K)

/-- The dimension of the class of a module is its dimension. -/
@[simp]
theorem dimension_of (M : FGLieModuleCat.{w} K L) :
    dimension K (SplitK0.of M) = finrank K M.obj :=
  SplitK0.lift_of _ M

/-! ### The character -/

variable [CharZero K] (H : LieSubalgebra K L)

section Nilpotent

variable [LieRing.IsNilpotent H]

/-- The formal character as an invariant of finite-dimensional Lie modules, additive on
biproducts. -/
private noncomputable def characterInvariant :
    SplitK0.AdditiveInvariant (FGLieModuleCat.{w} K L) (AddMonoidAlgebra ℤ (Dual K H)) where
  obj M := formalCharacter K H M.obj
  map_iso _ _ e := formalCharacter_congr ((isoToLieModuleEquiv e).restrictLie H)
  map_biprod M N := by
    rw [formalCharacter_congr ((biprodLieModuleEquiv M N).restrictLie H), formalCharacter_prod]

/-- **The formal character of a virtual finite-dimensional Lie module**: the homomorphism on the
split Grothendieck group sending `[M] - [N]` to `ch M - ch N`, the characters being read on the
nilpotent Lie subalgebra `H`. -/
noncomputable def character :
    SplitK0 (FGLieModuleCat.{w} K L) →+ AddMonoidAlgebra ℤ (Dual K H) :=
  SplitK0.lift (characterInvariant K H)

/-- The character of the class of a module is its formal character. -/
@[simp]
theorem character_of (M : FGLieModuleCat.{w} K L) :
    character K H (SplitK0.of M) = formalCharacter K H M.obj :=
  SplitK0.lift_of _ M

/-- **The augmentation of the character is the dimension.** Over an algebraically closed field,
the coefficients of the character of a virtual module add up to its dimension. -/
theorem sum_character_coeff_eq_dimension [IsAlgClosed K] (x : SplitK0 (FGLieModuleCat.{w} K L)) :
    ((character K H x).coeff.sum fun _ n ↦ n) = dimension K x := by
  induction x using SplitK0.induction_on with
  | zero => simp
  | of M => rw [character_of, dimension_of, sum_formalCharacter_coeff_eq_finrank]
  | add x y hx hy =>
      rw [map_add, map_add, AddMonoidAlgebra.coeff_add,
        Finsupp.sum_add_index' (fun _ ↦ rfl) fun _ _ _ ↦ rfl, hx, hy]
  | neg x hx =>
      rw [map_neg, map_neg, AddMonoidAlgebra.coeff_neg, Finsupp.sum_neg_index fun _ ↦ rfl,
        Finsupp.sum_neg, hx]

end Nilpotent

section Killing

variable {K} [IsKilling K L] [FiniteDimensional K L] [H.IsCartanSubalgebra]

/-- **The character of a virtual module is supported on integral weights.** A nonzero coefficient
of `ch M - ch N` is a nonzero coefficient of `ch M` or of `ch N`, hence a weight of `M` or `N`. -/
theorem isIntegralWeight_of_character_coeff_ne_zero [IsTriangularizable K H L]
    {x : SplitK0 (FGLieModuleCat.{w} K L)} {χ : Dual K H} (hχ : (character K H x).coeff χ ≠ 0) :
    IsIntegralWeight χ := by
  obtain ⟨M, N, rfl⟩ := SplitK0.exists_eq_sub x
  rw [map_sub, character_of, character_of, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply] at hχ
  by_cases hM : (formalCharacter K H M.obj).coeff χ = 0
  · exact isIntegralWeight_of_formalCharacter_coeff_ne_zero (M := N.obj) fun hN ↦
      hχ (by simp [hM, hN])
  · exact isIntegralWeight_of_formalCharacter_coeff_ne_zero hM

variable [IsAlgClosed K]

/-- **Weyl invariance of the character of a virtual module.** -/
theorem character_coeff_weylGroup_smul (w : (IsKilling.rootSystem H).weylGroup) (χ : Dual K H)
    (x : SplitK0 (FGLieModuleCat.{w} K L)) :
    (character K H x).coeff (w • χ) = (character K H x).coeff χ := by
  obtain ⟨M, N, rfl⟩ := SplitK0.exists_eq_sub x
  simp only [map_sub, character_of, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    formalCharacter_coeff_weylGroup_smul]

end Killing

end TauCeti.FGLieModuleCat
