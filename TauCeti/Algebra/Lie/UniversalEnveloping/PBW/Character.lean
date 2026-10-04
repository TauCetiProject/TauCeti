/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Character
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Decomposition

/-!
# Characters of a Lie subalgebra generate a proper left ideal

Let `B` be a Lie subalgebra of a Lie algebra `L` over a commutative ring `R`, and let
`χ : B → R` be a character of `B`. The elements `ι x - χ x` of `U(L)`, for `x : B`, generate a
left ideal of `U(L)`, and this file proves that the left ideal is **proper** as soon as `B` has a
complement in `L` and both `B` and the complement are free; over a field this holds for every Lie
subalgebra. In other words, the induced module `U(L) ⊗_{U(B)} R_χ`, presented as the quotient of
`U(L)` by that left ideal, is nonzero.

The input is the freeness half of the Poincaré--Birkhoff--Witt theorem relative to a subalgebra:
`U(L)` is a free right `U(B)`-module on the ordered monomials in a basis of a complement of `B`.
For a semisimple Lie algebra and its Borel subalgebra this is what makes Verma modules nonzero.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.span_range_ι_sub_algebraMap_ne_top_of_isCompl`: over a
  nontrivial commutative ring, if `B` has a complement and both are free, the left ideal generated
  by `ι x - χ x` is proper.
* `TauCeti.UniversalEnvelopingAlgebra.span_range_ι_sub_algebraMap_ne_top`: over a field, the same
  holds for every Lie subalgebra.

## Implementation notes

Choose an ordered basis of `L` that lists a basis of the complement `A` before a basis of `B`. By
PBW its ordered monomials form a basis of `U(L)`, and each of them factors as an ordered monomial
in the basis of `A` times the image of an ordered monomial of `U(B)`. The linear form on `U(L)`
that reads off the coefficient of the empty `A`-monomial and applies `χ` to it is then right
`U(B)`-semilinear along `χ`, so it kills the left ideal while sending `1` to `1`. Rather than
building the right `U(B)`-module structure, the file defines this linear form directly on the PBW
basis.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §17.4
  and §20.3.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open LieAlgebra Module

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w₁ w₂

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

section Adapted

variable (B : LieSubalgebra R L) {A : Submodule R L} (hA : IsCompl A (B : Submodule R L))
  {ιA : Type w₁} {ιB : Type w₂} (bA : Basis ιA R A) (bB : Basis ιB R B)

variable [LinearOrder ιA] [LinearOrder ιB]

/-- The ordered monomial in the basis of the complement with exponent vector `α`. -/
private noncomputable def complementMonomial (α : ιA →₀ ℕ) : U :=
  pbwMonomial R L (fun i ↦ (bA i : L)) (α.toMultiset.sort (· ≤ ·))

variable (χ : LieCharacter R B)

/-- The linear form on `U(L)` reading off the coefficient of the empty complement monomial in the
free right `U(B)`-module structure, and applying the character `χ` to it. -/
private noncomputable def characterForm : U →ₗ[R] R :=
  (B.relativePBWBasis hA bA bB).constr R fun n ↦
    if n.1 = 0 then
      _root_.UniversalEnvelopingAlgebra.lift R χ (bB.pbwBasis n.2)
    else 0

private theorem _root_.UniversalEnvelopingAlgebra.characterForm_complementMonomial_mul
    (α : ιA →₀ ℕ) (y : _root_.UniversalEnvelopingAlgebra R B) :
    characterForm B hA bA bB χ (complementMonomial bA α * map R B.incl y) =
      if α = 0 then _root_.UniversalEnvelopingAlgebra.lift R χ y else 0 := by
  have hlin := bB.pbwBasis.ext (f₁ := characterForm B hA bA bB χ ∘ₗ
      LinearMap.mulLeft R (complementMonomial bA α) ∘ₗ (map R B.incl).toLinearMap)
    (f₂ := if α = 0 then (_root_.UniversalEnvelopingAlgebra.lift R χ).toLinearMap else 0)
    fun β ↦ by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply]
      rw [complementMonomial, ← LieSubalgebra.relativePBWBasis_apply B hA, characterForm,
        Basis.constr_basis]
      split_ifs <;> simp
  have hy := LinearMap.congr_fun hlin y
  split_ifs at hy ⊢ <;> simpa using hy

/-- The character form is right `U(B)`-semilinear along the character `χ`. -/
private theorem _root_.UniversalEnvelopingAlgebra.characterForm_mul_map (u : U)
    (r : _root_.UniversalEnvelopingAlgebra R B) :
    characterForm B hA bA bB χ (u * map R B.incl r) =
      characterForm B hA bA bB χ u * _root_.UniversalEnvelopingAlgebra.lift R χ r := by
  have hlin := (B.relativePBWBasis hA bA bB).ext
    (f₁ := characterForm B hA bA bB χ ∘ₗ LinearMap.mulRight R (map R B.incl r))
    (f₂ := _root_.UniversalEnvelopingAlgebra.lift R χ r • characterForm B hA bA bB χ)
    fun n ↦ by
      rcases n with ⟨α, β⟩
      rw [LieSubalgebra.relativePBWBasis_apply, ← complementMonomial]
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.smul_apply,
        mul_assoc, ← map_mul,
        _root_.UniversalEnvelopingAlgebra.characterForm_complementMonomial_mul, smul_eq_mul]
      split_ifs <;> simp [mul_comm]
  simpa [mul_comm] using LinearMap.congr_fun hlin u

private theorem characterForm_one : characterForm B hA bA bB χ 1 = 1 := by
  simpa [complementMonomial] using
    _root_.UniversalEnvelopingAlgebra.characterForm_complementMonomial_mul B hA bA bB χ 0 1

include hA bA bB in
/-- The left ideal generated by `ι x - χ x` is proper, given ordered bases of `B` and of a
complement. -/
private theorem span_range_ι_sub_algebraMap_ne_top_of_basis [Nontrivial R] :
    Submodule.span U (Set.range fun x : B ↦
      _root_.UniversalEnvelopingAlgebra.ι R (x : L) - algebraMap R U (χ x)) ≠ ⊤ := by
  intro htop
  have key : ∀ s ∈ Submodule.span U (Set.range fun x : B ↦
      _root_.UniversalEnvelopingAlgebra.ι R (x : L) - algebraMap R U (χ x)),
      ∀ v : U, characterForm B hA bA bB χ (v * s) = 0 := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨x, rfl⟩ := hs
      intro v
      dsimp only
      have hx : _root_.UniversalEnvelopingAlgebra.ι R (x : L) - algebraMap R U (χ x) =
          map R B.incl (_root_.UniversalEnvelopingAlgebra.ι R x -
            algebraMap R (_root_.UniversalEnvelopingAlgebra R B) (χ x)) := by
        rw [map_sub, map_ι, AlgHom.commutes, LieSubalgebra.coe_incl]
      rw [hx, _root_.UniversalEnvelopingAlgebra.characterForm_mul_map]
      simp
    | zero => simp
    | add s t _ _ hs ht => simp [mul_add, hs, ht]
    | smul a s _ hs =>
      intro v
      rw [smul_eq_mul, ← mul_assoc]
      exact hs _
  have h1 := key 1 (htop ▸ Submodule.mem_top) 1
  rw [mul_one, characterForm_one] at h1
  exact one_ne_zero h1

end Adapted

section Free

variable (B : LieSubalgebra R L) (χ : LieCharacter R B)

/-- **A character of a Lie subalgebra generates a proper left ideal.** If the Lie subalgebra `B`
of `L` has a complement `A` and both are free, then for every character `χ` of `B` the elements
`ι x - χ x` of `U(L)`, for `x : B`, generate a proper left ideal of `U(L)`. Equivalently, the
induced module `U(L) ⊗_{U(B)} R_χ` is nonzero. -/
theorem span_range_ι_sub_algebraMap_ne_top_of_isCompl [Nontrivial R] {A : Submodule R L}
    (hA : IsCompl A (B : Submodule R L)) [Module.Free R A] [Module.Free R B] :
    Submodule.span U (Set.range fun x : B ↦
      _root_.UniversalEnvelopingAlgebra.ι R (x : L) - algebraMap R U (χ x)) ≠ ⊤ := by
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R A) := IsWellOrder.linearOrder WellOrderingRel
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R B) := IsWellOrder.linearOrder WellOrderingRel
  exact span_range_ι_sub_algebraMap_ne_top_of_basis B hA (Module.Free.chooseBasis R A)
    (Module.Free.chooseBasis R B) χ

end Free

section Field

/-- **A character of a Lie subalgebra generates a proper left ideal, over a field.** For every
Lie subalgebra `B` of a Lie algebra `L` over a field and every character `χ` of `B`, the elements
`ι x - χ x` of `U(L)`, for `x : B`, generate a proper left ideal of `U(L)`. -/
theorem span_range_ι_sub_algebraMap_ne_top {K : Type u} {L : Type v} [Field K] [LieRing L]
    [LieAlgebra K L] (B : LieSubalgebra K L) (χ : LieCharacter K B) :
    Submodule.span (_root_.UniversalEnvelopingAlgebra K L) (Set.range fun x : B ↦
      _root_.UniversalEnvelopingAlgebra.ι K (x : L) -
        algebraMap K (_root_.UniversalEnvelopingAlgebra K L) (χ x)) ≠ ⊤ := by
  obtain ⟨A, hA⟩ := Submodule.exists_isCompl (B : Submodule K L)
  exact span_range_ι_sub_algebraMap_ne_top_of_isCompl B χ hA.symm

end Field

end TauCeti.UniversalEnvelopingAlgebra
