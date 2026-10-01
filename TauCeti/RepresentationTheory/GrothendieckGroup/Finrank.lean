/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Free
public import TauCeti.RepresentationTheory.GrothendieckGroup.SimpleBasis

/-!
# The dimension homomorphism on the Grothendieck group of finite-length modules

Let `A` be a finite-dimensional algebra over a field `k`.  Every finitely generated `A`-module is
then finite-dimensional over `k`, and the `k`-dimension is additive in short exact sequences, so it
descends to a homomorphism `TauCeti.finrankK0 : G₀(mod A) →+ ℤ` out of the exact Grothendieck group
of `TauCeti.finiteModulesExactStructure`.  It is the invariant that turns a relation in `G₀(mod A)`
into an identity between dimensions, and in particular it detects the zero module.

Read in the simple-class basis of
`TauCeti/RepresentationTheory/GrothendieckGroup/SimpleBasis.lean`, the dimension of a class is the
sum of its Jordan--Hölder multiplicities weighted by the dimensions of the simple modules.  When
every simple module is isomorphic to one fixed line the dimension is an isomorphism
`G₀(mod A) ≃+ ℤ`.

The finite-dimensionality of `A` over `k` is essential and not cosmetic: `Module.finrank` has a junk
value on an infinite-dimensional space, so without it the function below is not additive.  The same
restriction appears, for the same reason, in `TauCeti.pathAlgebraDimensionVectorK0`.

## Main definitions

* `TauCeti.finrankK0`: the `k`-dimension as a homomorphism `G₀(mod A) →+ ℤ`.
* `TauCeti.finrankK0Equiv`: the isomorphism `G₀(mod A) ≃+ ℤ` when every simple `A`-module is
  isomorphic to one fixed line.

## Main results

* `TauCeti.finrankK0_of`: the dimension of an object class is the dimension of the module.
* `TauCeti.finrankK0_unique`: the dimension homomorphism is the only one with that property.
* `TauCeti.finrankK0_of_eq_zero_iff` and `TauCeti.finrankK0_of_pos`: the dimension of an object
  class vanishes exactly for the zero module, and is positive otherwise.
* `TauCeti.finrankK0_eq_sum_jordanHolderCoordinate_mul`: the dimension of a class is the sum of its
  Jordan--Hölder multiplicities weighted by the dimensions of the simple modules.
* `TauCeti.eq_finrankK0_smul_of_finrank_eq_one`: when every simple module is isomorphic to one
  fixed line, every class is an integer multiple of that line's class.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 6.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

universe u v

/-! ### The dimension homomorphism -/

section Finrank

variable (k : Type u) [Field k] (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **A finitely generated module over a finite-dimensional algebra is finite-dimensional over the
base field.** This is what makes `Module.finrank` over the base field an honest invariant of such a
module rather than a junk value. -/
theorem finiteDimensional_fgModuleCat_obj (M : FGModuleCat.{u} A) : FiniteDimensional k M.obj :=
  Module.Finite.trans A (M.obj : Type u)

private noncomputable def moduleFinrankInvariant :
    ExactK0.AdditiveInvariant (finiteModulesExactStructure A) ℤ where
  obj M := (Module.finrank k M.obj : ℤ)
  map_conflation {T} hT := by
    have hshort := (finiteModulesExactStructure_conflation_iff A T).mp hT
    have hexact : Function.Exact (LinearMap.restrictScalars k T.f.hom.hom)
        (LinearMap.restrictScalars k T.g.hom.hom) :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hshort.exact
    have h₁ := finiteDimensional_fgModuleCat_obj k A T.X₁
    have h₃ := finiteDimensional_fgModuleCat_obj k A T.X₃
    exact_mod_cast ModuleCat.free_shortExact_finrank_add
      (ModuleCat.shortComplex_shortExact
        (ModuleCat.shortComplexOfCompEqZero _ _ hexact.linearMap_comp_eq_zero) hexact
        hshort.moduleCat_injective_f hshort.moduleCat_surjective_g) rfl rfl

/-- **The dimension homomorphism** on the Grothendieck group of the finitely generated modules over
a finite-dimensional algebra: on the class of `M` it is `dim_k M`. -/
noncomputable def finrankK0 : ExactK0 (finiteModulesExactStructure A) →+ ℤ :=
  ExactK0.lift (moduleFinrankInvariant k A)

/-- The dimension homomorphism sends the class of a module to its dimension over the base field. -/
@[simp]
theorem finrankK0_of (M : FGModuleCat.{u} A) :
    finrankK0 k A (ExactK0.of M) = Module.finrank k M.obj :=
  ExactK0.lift_of (moduleFinrankInvariant k A) M

/-- The dimension homomorphism is the only homomorphism to `ℤ` returning the dimension on object
classes. -/
theorem finrankK0_unique (f : ExactK0 (finiteModulesExactStructure A) →+ ℤ)
    (hf : ∀ M : FGModuleCat.{u} A, f (ExactK0.of M) = Module.finrank k M.obj) :
    f = finrankK0 k A :=
  ExactK0.lift_unique (moduleFinrankInvariant k A) f hf

/-- Object classes have nonnegative dimension. -/
theorem finrankK0_of_nonneg (M : FGModuleCat.{u} A) : 0 ≤ finrankK0 k A (ExactK0.of M) := by
  simp only [finrankK0_of]
  positivity

/-- **The dimension homomorphism detects the zero module**: the class of `M` has dimension zero
exactly when `M` is the zero module. -/
theorem finrankK0_of_eq_zero_iff (M : FGModuleCat.{u} A) :
    finrankK0 k A (ExactK0.of M) = 0 ↔ Subsingleton M.obj := by
  have := finiteDimensional_fgModuleCat_obj k A M
  rw [finrankK0_of, Int.natCast_eq_zero, Module.finrank_zero_iff (R := k)]

/-- A nonzero module has a class of positive dimension. -/
theorem finrankK0_of_pos (M : FGModuleCat.{u} A) (hM : Nontrivial M.obj) :
    0 < finrankK0 k A (ExactK0.of M) :=
  lt_of_le_of_ne (finrankK0_of_nonneg k A M) fun h ↦
    (not_subsingleton_iff_nontrivial.2 hM) ((finrankK0_of_eq_zero_iff k A M).1 h.symm)

end Finrank

/-! ### The dimension homomorphism in the simple-class basis -/

section SimpleCoordinates

-- `[IsArtinianRing A]` follows from `[FiniteDimensional k A]`, but `TauCeti.jordanHolderCoordinate`
-- and `TauCeti.IsExhaustiveSimpleFamily` take it as an instance argument and both appear in the
-- statements below, so it cannot be confined to the proofs; and an instance deriving it from
-- `[FiniteDimensional k A]` has no synthesization order, since `k` is not determined by the goal.
variable (k : Type u) [Field k] (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsArtinianRing A] {I : Type v} (S : I → FGModuleCat.{u} A) [∀ i, IsSimpleModule A (S i)]
  (hnoniso : Pairwise fun i j ↦ IsEmpty ((S i : Type u) ≃ₗ[A] S j))
  (hexhaustive : IsExhaustiveSimpleFamily S)

include hnoniso hexhaustive in
/-- **The dimension of a class is its Jordan--Hölder expansion weighted by the dimensions of the
simple modules.** For the class of a module this is the statement that the dimension of a module is
the sum of the dimensions of its composition factors. -/
theorem finrankK0_eq_sum_jordanHolderCoordinate_mul [Fintype I]
    (x : ExactK0 (finiteModulesExactStructure A)) :
    finrankK0 k A x =
      ∑ i, jordanHolderCoordinate A (S i) x * (Module.finrank k (S i).obj : ℤ) := by
  classical
  set b := simpleClassBasis S hnoniso hexhaustive with hb
  calc finrankK0 k A x = finrankK0 k A (∑ i, b.repr x i • b i) := by rw [b.sum_repr x]
    _ = ∑ i, b.repr x i • finrankK0 k A (b i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ map_zsmul _ _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hb, simpleClassBasis_apply, simpleClassBasis_repr_apply, finrankK0_of, smul_eq_mul]

end SimpleCoordinates

/-! ### Algebras whose simple modules are all isomorphic to one line -/

section UniqueSimple

-- `[IsArtinianRing A]` follows from `[FiniteDimensional k A]`, but
-- `TauCeti.IsExhaustiveSimpleFamily` takes it as an instance argument and appears in the statements
-- below, so it cannot be confined to the proofs; and an instance deriving it from
-- `[FiniteDimensional k A]` has no synthesization order, since `k` is not determined by the goal.
variable (k : Type u) [Field k] (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsArtinianRing A] (S : FGModuleCat.{u} A)
  (hexhaustive : IsExhaustiveSimpleFamily fun _ : Unit ↦ S)

include hexhaustive in
/-- **Every class is an integer multiple of the class of `S`** when every simple module is
isomorphic to `S` and `S` is a line. The multiple is then the dimension itself. Simplicity of `S` is
not needed: exhaustiveness of the one-member family already says that `S` is the only simple module
up to isomorphism, which is what the composition-series induction behind
`TauCeti.span_range_exactK0OfFamily_eq_top` consumes. -/
theorem eq_finrankK0_smul_of_finrank_eq_one (hdim : Module.finrank k S.obj = 1)
    (x : ExactK0 (finiteModulesExactStructure A)) : x = finrankK0 k A x • ExactK0.of S := by
  have hrange : Set.range (exactK0OfFamily fun _ : Unit ↦ S) = {ExactK0.of S} := by
    ext y
    refine ⟨?_, ?_⟩
    · rintro ⟨i, rfl⟩
      exact exactK0OfFamily_apply _ i
    · rintro rfl
      exact ⟨(), exactK0OfFamily_apply _ ()⟩
  have hmem : x ∈
      Submodule.span ℤ ({ExactK0.of S} : Set (ExactK0 (finiteModulesExactStructure A))) := by
    rw [← hrange, span_range_exactK0OfFamily_eq_top _ hexhaustive]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  have hcoord : finrankK0 k A x = c := by
    rw [← hc, map_zsmul, finrankK0_of, hdim, Nat.cast_one, smul_eq_mul, mul_one]
  rw [hcoord, hc]

include hexhaustive in
/-- The dimension homomorphism is bijective when every simple module is isomorphic to the line
`S`. -/
theorem finrankK0_bijective_of_finrank_eq_one (hdim : Module.finrank k S.obj = 1) :
    Function.Bijective (finrankK0 k A) := by
  constructor
  · intro x y hxy
    rw [eq_finrankK0_smul_of_finrank_eq_one k A S hexhaustive hdim x,
      eq_finrankK0_smul_of_finrank_eq_one k A S hexhaustive hdim y, hxy]
  · intro n
    refine ⟨n • ExactK0.of S, ?_⟩
    rw [map_zsmul, finrankK0_of, hdim, Nat.cast_one, smul_eq_mul, mul_one]

/-- **`G₀(mod A) ≃+ ℤ` when every simple module is isomorphic to the line `S`**, the isomorphism
being the dimension.  The group algebra of a finite `ℓ`-group over a field of characteristic `ℓ`,
whose only simple module is the trivial one, is an instance. -/
noncomputable def finrankK0Equiv (hdim : Module.finrank k S.obj = 1) :
    ExactK0 (finiteModulesExactStructure A) ≃+ ℤ :=
  AddEquiv.ofBijective (finrankK0 k A)
    (finrankK0_bijective_of_finrank_eq_one k A S hexhaustive hdim)

@[simp]
theorem finrankK0Equiv_apply (hdim : Module.finrank k S.obj = 1)
    (x : ExactK0 (finiteModulesExactStructure A)) :
    finrankK0Equiv k A S hexhaustive hdim x = finrankK0 k A x :=
  (rfl)

@[simp]
theorem finrankK0Equiv_symm_apply (hdim : Module.finrank k S.obj = 1) (n : ℤ) :
    (finrankK0Equiv k A S hexhaustive hdim).symm n = n • ExactK0.of S := by
  rw [AddEquiv.symm_apply_eq, finrankK0Equiv_apply, map_zsmul, finrankK0_of, hdim, Nat.cast_one,
    smul_eq_mul, mul_one]

end UniqueSimple

end TauCeti
