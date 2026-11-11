/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.ExtEuler
public import TauCeti.Algebra.Module.ProjectiveCover.Multiplicity
public import TauCeti.RepresentationTheory.GrothendieckGroup.CartanMatrix
import TauCeti.RingTheory.Semisimple.Schur

/-!
# Projective/simple duality for the Euler form

Let `A` be a finite-dimensional algebra over a field `k`, and let `f : P ⟶ S` be a projective
cover of a simple module. On classes, the Euler form `χ = TauCeti.projectiveExtEuler` between
`K₀(proj A)` and `G₀(mod A)` is the Hom dimension, so the multiplicity formula
`dim_k Hom_A(P, M) = [M : S] · dim_k End_A(S)` says that pairing against `[P]` reads the
Jordan--Hölder coordinate of `S`, scaled by the dimension of the division algebra `End_A(S)`.

Choose exhaustive families of pairwise nonisomorphic indecomposable projectives `Pᵢ` and simples
`Sᵢ`, with `Pᵢ ⟶ Sᵢ` a projective cover, and put `dᵢ = dim_k End_A(Sᵢ)`. Then the Euler form and
the integral multiplicity pairing `⟨-, -⟩ = TauCeti.projectiveSimplePairing` differ exactly by
these scalars:

```text
χ([Pᵢ], y) = ⟨[Pᵢ], y⟩ · dᵢ,    χ(x, [Sᵢ]) = ⟨x, [Sᵢ]⟩ · dᵢ.
```

Every `dᵢ` is positive, so both radicals of `χ` vanish over every field. The multiplicity pairing
is perfect, but `χ` is perfect only when every `dᵢ = 1`, which is also exactly when `χ` equals the
multiplicity pairing: the raw Hom dimension computes the multiplicity pairing precisely for
absolutely simple simples. Over a field that does not split the simple modules, the multiplicity
coordinate, rather than the Hom dimension, is the perfect pairing. The graded counterpart is
`TauCeti.gradedProjectiveExtEuler_bijective_iff`.

## Main results

* `TauCeti.IsProjectiveCover.projectiveExtEuler_of_eq_jordanHolderCoordinate_mul`:
  `χ([P], y) = [y : S] · dim_k End_A(S)` for a projective cover `P ⟶ S`.
* `TauCeti.projectiveExtEuler_of_left_eq_projectiveSimplePairing_mul` and
  `TauCeti.projectiveExtEuler_of_right_eq_projectiveSimplePairing_mul`: the Euler form is the
  multiplicity pairing scaled by `dᵢ`, against `[Pᵢ]` on the left and `[Sᵢ]` on the right.
* `TauCeti.projectiveExtEuler_eq_projectiveSimplePairing_iff`: the Euler form is the multiplicity
  pairing if and only if every simple has one-dimensional endomorphism algebra.
* `TauCeti.projectiveExtEuler_nondegenerate`: both radicals of the Euler form vanish.
* `TauCeti.projectiveExtEuler_isPerfPair_iff`: the Euler form is a perfect pairing if and only if
  every simple has one-dimensional endomorphism algebra.

## References

* Peter Webb, *A Course in Finite Group Representation Theory*, Chapter 7, Section 7.4,
  Proposition 7.4.1 and Corollary 7.4.2, for the factor `dim_k End_A(S)` over a general field.
* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3, for the Euler form and the Cartan matrix over an
  algebraically closed field.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] [Module.Finite k A]
  [IsArtinianRing A]

/-! ### Pairing against a projective cover -/

/-- **Pairing against a projective cover reads composition multiplicities.** For a projective
cover `P ⟶ S` of a simple module, `χ([P], y)` is the Jordan--Hölder coordinate of `S` in `y`
times `dim_k End_A(S)`. On a class `[M]` this is the multiplicity formula
`dim_k Hom_A(P, M) = [M : S] · dim_k End_A(S)`. -/
theorem IsProjectiveCover.projectiveExtEuler_of_eq_jordanHolderCoordinate_mul
    {P : (finiteProjectiveModules A).FullSubcategory} {S : FGModuleCat.{u} A}
    [IsSimpleModule A S] {f : P.obj →ₗ[A] S} (hf : IsProjectiveCover f)
    (y : ExactK0.{u} (finiteModulesExactStructure A)) :
    projectiveExtEuler k A (ExactK0.of P) y =
      jordanHolderCoordinate A S y * Module.finrank k (Module.End A S) := by
  induction y using ExactK0.induction_on with
  | zero => simp
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', add_mul]
  | neg y hy => rw [map_neg, map_neg, hy, neg_mul]
  | of M =>
    have : Module.Finite A M.obj := (ModuleCat.isFG_iff M.obj).mp M.property
    have : Module.Finite k M.obj := Module.Finite.trans A M.obj
    have : IsNoetherian A M.obj := isNoetherian_of_tower k inferInstance
    have : IsArtinian A M.obj := isArtinian_of_tower k inferInstance
    rw [projectiveExtEuler_of_of, jordanHolderCoordinate_of,
      hf.finrank_linearMap_eq_jordanHolderMultiplicity_mul_finrank_end M.obj, Nat.cast_mul]

/-! ### Comparison with the multiplicity pairing -/

variable {I : Type v}
variable (P : I → (finiteProjectiveModules A).FullSubcategory)
variable (S : I → FGModuleCat.{u} A) [hS : ∀ i, IsSimpleModule A (S i)]
variable (hind : ∀ i, IsIndecomposableModule A (P i).obj)
variable (hPnoniso : Pairwise fun i j ↦ IsEmpty (↥(P i).obj ≃ₗ[A] ↥(P j).obj))
variable (hPexhaustive : IsExhaustiveIndecomposableProjectiveFamily P)
variable (hSnoniso : Pairwise fun i j ↦ IsEmpty ((S i : Type u) ≃ₗ[A] S j))
variable (hSexhaustive : IsExhaustiveSimpleFamily S)
variable {f : ∀ i, (P i).obj →ₗ[A] S i} (hf : ∀ i, IsProjectiveCover (f i))

include hf in
/-- **The Euler form against a projective cover is the scaled multiplicity pairing**:
`χ([Pᵢ], y) = ⟨[Pᵢ], y⟩ · dim_k End_A(Sᵢ)`. -/
theorem projectiveExtEuler_of_left_eq_projectiveSimplePairing_mul (i : I)
    (y : ExactK0.{u} (finiteModulesExactStructure A)) :
    projectiveExtEuler k A (ExactK0.of (P i)) y =
      projectiveSimplePairing P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive
          (ExactK0.of (P i)) y *
        Module.finrank k (Module.End A (S i)) := by
  rw [projectiveSimplePairing_of_left,
    (hf i).projectiveExtEuler_of_eq_jordanHolderCoordinate_mul]

include hf in
/-- **The Euler form against a simple class is the scaled multiplicity pairing**:
`χ(x, [Sᵢ]) = ⟨x, [Sᵢ]⟩ · dim_k End_A(Sᵢ)`. The scalar is attached to the simple `Sᵢ`, so it
does not depend on the projective class `x`. -/
theorem projectiveExtEuler_of_right_eq_projectiveSimplePairing_mul
    (x : ExactK0.{u} (finiteProjectiveModulesExactStructure A)) (i : I) :
    projectiveExtEuler k A x (ExactK0.of (S i)) =
      projectiveSimplePairing P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive
          x (ExactK0.of (S i)) *
        Module.finrank k (Module.End A (S i)) := by
  classical
  -- Both sides are linear in `x`; compare them on the basis `[Pⱼ]`, where the multiplicity
  -- pairing is the Kronecker delta.
  have key : (projectiveExtEuler k A).flip (ExactK0.of (S i)) =
      (Module.finrank k (Module.End A (S i)) : ℤ) •
        (projectiveSimplePairing P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive).flip
          (ExactK0.of (S i)) := by
    refine (indecomposableProjectiveClassBasis P hind hPnoniso hPexhaustive).ext fun j ↦ ?_
    rw [LinearMap.smul_apply, LinearMap.flip_apply, LinearMap.flip_apply,
      indecomposableProjectiveClassBasis_apply,
      projectiveExtEuler_of_left_eq_projectiveSimplePairing_mul P S hind hPnoniso hPexhaustive
        hSnoniso hSexhaustive hf, projectiveSimplePairing_basis, smul_eq_mul]
    split_ifs with hji
    · subst hji
      ring
    · simp
  rw [← LinearMap.flip_apply (projectiveExtEuler k A), key, LinearMap.smul_apply,
    LinearMap.flip_apply, smul_eq_mul, mul_comm]

include hf in
/-- **The Euler form is the multiplicity pairing exactly for absolutely simple simples**:
`χ = ⟨-, -⟩` if and only if `dim_k End_A(Sᵢ) = 1` for every `i`, for instance over an
algebraically closed field. -/
theorem projectiveExtEuler_eq_projectiveSimplePairing_iff :
    projectiveExtEuler k A =
        projectiveSimplePairing P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive ↔
      ∀ i, Module.finrank k (Module.End A (S i)) = 1 := by
  classical
  constructor
  · intro h i
    have hi := LinearMap.congr_fun₂ h (ExactK0.of (P i)) (ExactK0.of (S i))
    rw [projectiveExtEuler_of_left_eq_projectiveSimplePairing_mul P S hind hPnoniso hPexhaustive
      hSnoniso hSexhaustive hf, projectiveSimplePairing_basis] at hi
    simpa using hi
  · intro h
    refine (indecomposableProjectiveClassBasis P hind hPnoniso hPexhaustive).ext
      fun i ↦ LinearMap.ext fun y ↦ ?_
    rw [indecomposableProjectiveClassBasis_apply,
      projectiveExtEuler_of_left_eq_projectiveSimplePairing_mul P S hind hPnoniso hPexhaustive
        hSnoniso hSexhaustive hf, h i, Nat.cast_one, mul_one]

/-! ### Nondegeneracy and perfectness -/

omit [IsArtinianRing A] in
/-- The scale `dim_k End_A(T)` of a finitely generated simple module is a nonzero integer. -/
private theorem finrank_end_ne_zero (T : FGModuleCat.{u} A) [IsSimpleModule A T] :
    (Module.finrank k (Module.End A T) : ℤ) ≠ 0 := by
  have : Module.Finite A T := (ModuleCat.isFG_iff T.obj).mp T.property
  have : Module.Finite k T := Module.Finite.trans A (T : Type u)
  exact mod_cast (finrank_end_pos (k := k) (A := A) (S := T)).ne'

variable [Finite I]

include hind hPnoniso hPexhaustive hSnoniso hSexhaustive hf in
/-- The Euler form separates projective classes. -/
theorem projectiveExtEuler_injective : Function.Injective (projectiveExtEuler k A) := by
  have := projectiveSimplePairing_isPerfPair P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive
  intro x x' hx
  apply (LinearMap.IsPerfPair.bijective_left
    (projectiveSimplePairing P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive)).injective
  refine (simpleClassBasis S hSnoniso hSexhaustive).ext fun i ↦ ?_
  have hd := finrank_end_ne_zero (k := k) (S i)
  have hi := LinearMap.congr_fun hx (ExactK0.of (S i))
  rw [projectiveExtEuler_of_right_eq_projectiveSimplePairing_mul P S hind hPnoniso hPexhaustive
      hSnoniso hSexhaustive hf, projectiveExtEuler_of_right_eq_projectiveSimplePairing_mul P S hind
      hPnoniso hPexhaustive hSnoniso hSexhaustive hf] at hi
  rw [simpleClassBasis_apply]
  exact mul_right_cancel₀ hd hi

include hind hPnoniso hPexhaustive hSnoniso hSexhaustive hf in
/-- The Euler form separates module classes. -/
theorem projectiveExtEuler_flip_injective :
    Function.Injective (projectiveExtEuler k A).flip := by
  have := projectiveSimplePairing_isPerfPair P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive
  intro y y' hy
  apply (LinearMap.IsPerfPair.bijective_right
    (projectiveSimplePairing P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive)).injective
  refine (indecomposableProjectiveClassBasis P hind hPnoniso hPexhaustive).ext fun i ↦ ?_
  have hd := finrank_end_ne_zero (k := k) (S i)
  have hi := LinearMap.congr_fun hy (indecomposableProjectiveClassBasis P hind hPnoniso
    hPexhaustive i)
  rw [indecomposableProjectiveClassBasis_apply] at hi ⊢
  rw [LinearMap.flip_apply, LinearMap.flip_apply,
    projectiveExtEuler_of_left_eq_projectiveSimplePairing_mul P S hind hPnoniso hPexhaustive
      hSnoniso hSexhaustive hf, projectiveExtEuler_of_left_eq_projectiveSimplePairing_mul P S hind
      hPnoniso hPexhaustive hSnoniso hSexhaustive hf] at hi
  rw [LinearMap.flip_apply, LinearMap.flip_apply]
  exact mul_right_cancel₀ hd hi

include hind hPnoniso hPexhaustive hSnoniso hSexhaustive hf in
/-- **Both radicals of the Euler form vanish**, over every field. This does not identify either
Grothendieck group with the dual of the other; see `TauCeti.projectiveExtEuler_isPerfPair_iff`. -/
theorem projectiveExtEuler_nondegenerate : (projectiveExtEuler k A).Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot]
    exact LinearMap.ker_eq_bot_of_injective
      (projectiveExtEuler_injective P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive hf)
  · rw [LinearMap.separatingRight_iff_flip_ker_eq_bot]
    exact LinearMap.ker_eq_bot_of_injective
      (projectiveExtEuler_flip_injective P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive hf)

include hind hPnoniso hPexhaustive hSnoniso hSexhaustive hf in
/-- **The Euler form is perfect exactly for absolutely simple simples**: it identifies either
Grothendieck group with the integral dual of the other if and only if `dim_k End_A(Sᵢ) = 1` for
every `i`. Otherwise the coordinate functional of `[Sᵢ]` is not of the form `χ(x, -)`, since
every value `χ(x, [Sᵢ])` is divisible by `dim_k End_A(Sᵢ)`. -/
theorem projectiveExtEuler_isPerfPair_iff :
    (projectiveExtEuler k A).IsPerfPair ↔ ∀ i, Module.finrank k (Module.End A (S i)) = 1 := by
  classical
  constructor
  · intro h i
    obtain ⟨x, hx⟩ := (LinearMap.IsPerfPair.bijective_left (projectiveExtEuler k A)).2
      ((simpleClassBasis S hSnoniso hSexhaustive).coord i)
    have hi := LinearMap.congr_fun hx (ExactK0.of (S i))
    rw [projectiveExtEuler_of_right_eq_projectiveSimplePairing_mul P S hind hPnoniso hPexhaustive
        hSnoniso hSexhaustive hf, ← simpleClassBasis_apply S hSnoniso hSexhaustive,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same] at hi
    exact_mod_cast Int.eq_one_of_mul_eq_one_left (Int.natCast_nonneg _) hi
  · intro h
    rw [(projectiveExtEuler_eq_projectiveSimplePairing_iff P S hind hPnoniso hPexhaustive hSnoniso
      hSexhaustive hf).2 h]
    exact projectiveSimplePairing_isPerfPair P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive

end TauCeti
