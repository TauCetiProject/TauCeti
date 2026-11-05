/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.CategoryTheory.Preadditive.Schur
public import TauCeti.CategoryTheory.Semisimple.Basic
public import TauCeti.CategoryTheory.Simple.Classes

/-!
# Dual bases of morphisms out of simple objects

Let `S` be a simple object of a `k`-linear category over an algebraically closed field `k`, with
finite-dimensional endomorphisms. By Schur's lemma every endomorphism of `S` is a scalar, so for
every object `X` composition defines a bilinear pairing (see
`TauCeti.CategoryTheory.Preadditive.Schur`)

`TauCeti.homPairing k S X : (S ⟶ X) × (X ⟶ S) → k`,  `f ≫ g = homPairing k S X f g • 𝟙 S`.

In a finite semisimple abelian category this pairing is perfect: a nonzero morphism out of `S`
is a split monomorphism, and a nonzero morphism into `S` is a split epimorphism. Hence every
basis `b` of `S ⟶ X` has a dual basis `b.homDual` of `X ⟶ S`, characterized by
`b i ≫ b.homDual j = if i = j then 𝟙 S else 0`.

These dual bases satisfy the **completeness relation**: choosing for each simple class `S` a
basis `b S` of morphisms from its representative into `X`,

`∑ S, ∑ i, (b S).homDual i ≫ b S i = 𝟙 X`.

The element `∑ i, b.homDual i ⊗ b i` of `(X ⟶ S) ⊗ (S ⟶ X)` does not depend on the basis, and
it is natural in `X`: for `h : A ⟶ A'` and any bilinear map `β`,

`∑ i, β (a.homDual i) (a i ≫ h) = ∑ j, β (h ≫ a'.homDual j) (a' j)`.

Combining the two, a sum over a basis of `S ⟶ F.obj B`, for an additive functor `F`, can be
computed through the simple constituents `T` of `B`, using bases of `S ⟶ F.obj T` and `T ⟶ B`.

These identities are the linear algebra behind sums of the shape `∑ i, b i ⊗ … ⊗ b.homDual i`
in a fusion category, such as the half-braiding of the object `⨁ S, S ⊗ X ⊗ Sᘁ` of the Drinfeld
centre: naturality of the canonical element gives naturality in the braided object, and the
factorization through simple constituents gives compatibility with tensor products.

## Main declarations

* `TauCeti.isPerfPair_homPairing`: in a finite semisimple category the pairing is perfect;
* `Module.Basis.homDual`: the dual basis of `X ⟶ S` of a basis of `S ⟶ X`, characterized by
  `Module.Basis.apply_comp_homDual` and `Module.Basis.eq_homDual_iff`, with coordinates computed
  by `Module.Basis.comp_homDual` and `Module.Basis.homDual_repr`;
* `TauCeti.sum_sum_homDual_comp_eq_id`: the completeness relation;
* `Module.Basis.sum_homDual_comp`: naturality of the canonical element, and
  `Module.Basis.sum_homDual_eq` its independence of the basis;
* `TauCeti.sum_homDual_eq_sum_map_homDual`: the canonical element computed through the simple
  constituents of an object.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§1.8, 7.13
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Module

universe w v u v' u'

namespace TauCeti

section Perfect

variable {k : Type w} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [IsFiniteSemisimpleCategory C]

/-- In a finite semisimple category, the composition pairing between morphisms out of and into
a simple object is perfect. -/
instance isPerfPair_homPairing (S X : C) [Simple S] [FiniteDimensional k (S ⟶ S)]
    [FiniteDimensional k (S ⟶ X)] : (homPairing k S X).IsPerfPair := by
  refine .of_injective ((injective_iff_map_eq_zero _).2 fun f hf ↦ ?_)
    ((injective_iff_map_eq_zero _).2 fun g hg ↦ ?_)
  · -- A nonzero morphism out of `S` has a retraction, which pairs with it to `1`.
    by_contra hf₀
    have := isSplitMono_of_nonzero_from_simple hf₀
    have h := (homPairing_eq_iff (k := k) f (retraction f) 1).2 (by simp)
    rw [hf, LinearMap.zero_apply] at h
    exact zero_ne_one h
  · -- A nonzero morphism into `S` has a section, which pairs with it to `1`.
    by_contra hg₀
    have := isSplitEpi_of_nonzero_to_simple hg₀
    have h := (homPairing_eq_iff (k := k) (section_ g) g 1).2 (by simp)
    rw [← LinearMap.flip_apply (homPairing k S X), hg, LinearMap.zero_apply] at h
    exact zero_ne_one h

end Perfect

end TauCeti

namespace Module.Basis

open TauCeti

variable {k : Type w} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [IsFiniteSemisimpleCategory C]
variable {S X : C} [Simple S] [FiniteDimensional k (S ⟶ S)]

section Dual

variable {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι k (S ⟶ X))

/-- The basis of `X ⟶ S` dual to a basis `b` of `S ⟶ X` under the composition pairing:
`b i ≫ b.homDual j` is `𝟙 S` if `i = j` and `0` otherwise. -/
def homDual : Basis ι k (X ⟶ S) :=
  have : FiniteDimensional k (S ⟶ X) := Module.Finite.of_basis b
  b.dualBasis.map (homPairing k S X).flip.toPerfPair.symm

/-- Pairing with the dual basis computes coordinates in the basis. -/
@[simp]
theorem homPairing_homDual (f : S ⟶ X) (i : ι) :
    homPairing k S X f (b.homDual i) = b.repr f i := by
  have : FiniteDimensional k (S ⟶ X) := Module.Finite.of_basis b
  rw [homDual, Basis.map_apply, LinearMap.apply_toPerfPair_flip, Basis.dualBasis_apply]

/-- Composing with an element of the dual basis extracts a coordinate. -/
theorem comp_homDual (f : S ⟶ X) (i : ι) : f ≫ b.homDual i = b.repr f i • 𝟙 S := by
  rw [← homPairing_smul_id (k := k), homPairing_homDual]

/-- A basis and its dual basis compose to the identity or to zero. -/
@[simp]
theorem apply_comp_homDual (i j : ι) : b i ≫ b.homDual j = if i = j then 𝟙 S else 0 := by
  rw [comp_homDual, repr_self, Finsupp.single_apply]
  split_ifs <;> simp

/-- The coordinates of a morphism into `S` in the dual basis are its pairings with the basis. -/
@[simp]
theorem homDual_repr (g : X ⟶ S) (i : ι) : b.homDual.repr g i = homPairing k S X (b i) g := by
  have : FiniteDimensional k (S ⟶ X) := Module.Finite.of_basis b
  rw [homDual, Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    Basis.dualBasis_repr, LinearMap.toPerfPair_apply, LinearMap.flip_apply]

/-- The dual basis is characterized by its composites with the basis. -/
theorem eq_homDual_iff (g : X ⟶ S) (j : ι) :
    g = b.homDual j ↔ ∀ i, b i ≫ g = if i = j then 𝟙 S else 0 := by
  refine ⟨by rintro rfl i; exact b.apply_comp_homDual i j, fun h ↦ b.homDual.ext_elem fun i ↦ ?_⟩
  rw [homDual_repr, homDual_repr, homPairing_homDual, repr_self, Finsupp.single_apply,
    homPairing_eq_iff, h i]
  split_ifs <;> simp_all [eq_comm]

end Dual

section Naturality

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] {A A' : C}
variable {M : Type*} [AddCommGroup M] [Module k M]

/-- The canonical element `∑ i, a.homDual i ⊗ a i` of `(A ⟶ S) ⊗ (S ⟶ A)` is natural in `A`:
for `h : A ⟶ A'`, bases `a` of `S ⟶ A` and `a'` of `S ⟶ A'`, and a bilinear map `β`, moving `h`
from the basis of `S ⟶ A` to the dual basis of `A' ⟶ S` does not change the sum. -/
theorem sum_homDual_comp (a : Basis ι k (S ⟶ A)) (a' : Basis ι' k (S ⟶ A')) (h : A ⟶ A')
    (β : (A ⟶ S) →ₗ[k] (S ⟶ A') →ₗ[k] M) :
    ∑ i, β (a.homDual i) (a i ≫ h) = ∑ j, β (h ≫ a'.homDual j) (a' j) := by
  -- Expand `a i ≫ h` in the basis `a'` and `h ≫ a'.homDual j` in the basis `a.homDual`; both
  -- sides become `∑ i, ∑ j, c i j • β (a.homDual i) (a' j)` with `c i j` the pairing of
  -- `a i ≫ h ≫ a'.homDual j`.
  conv_lhs => enter [2, i]; rw [← a'.sum_repr (a i ≫ h)]
  conv_rhs => enter [2, j]; rw [← a.homDual.sum_repr (h ≫ a'.homDual j)]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, ← homPairing_homDual,
    homDual_repr, homPairing_comp]
  exact Finset.sum_comm

/-- The canonical element `∑ i, b.homDual i ⊗ b i` does not depend on the basis `b`. -/
theorem sum_homDual_eq (a : Basis ι k (S ⟶ X)) (a' : Basis ι' k (S ⟶ X))
    (β : (X ⟶ S) →ₗ[k] (S ⟶ X) →ₗ[k] M) :
    ∑ i, β (a.homDual i) (a i) = ∑ j, β (a'.homDual j) (a' j) := by
  simpa using a.sum_homDual_comp a' (𝟙 X) β

end Naturality

end Module.Basis

namespace TauCeti

open SimpleClasses

variable {k : Type w} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [IsFiniteSemisimpleCategory C]
  [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

/-- **The completeness relation.** In a finite semisimple category with finitely many simple
classes, choose for every simple class `S` a basis `b S` of the morphisms from its representative
into `X`. Then the identity of `X` is the sum, over the simple classes and the basis elements,
of the composites of the dual basis elements with the basis elements. -/
theorem sum_sum_homDual_comp_eq_id [Fintype (SimpleClasses C)] (X : C)
    {ι : SimpleClasses C → Type*} [∀ S, Fintype (ι S)] [∀ S, DecidableEq (ι S)]
    (b : ∀ S : SimpleClasses C, Basis (ι S) k (S.repr ⟶ X)) :
    ∑ S, ∑ i, (b S).homDual i ≫ b S i = 𝟙 X := by
  classical
  refine (𝟭 C).hom_ext_of_simple fun T _ t ↦ ?_
  simp only [Functor.id_map]
  -- Reduce to morphisms out of the representative `R` of the class of `T`.
  suffices H : ∀ s : (classOf T).repr ⟶ X, s ≫ ∑ S, ∑ i, (b S).homDual i ≫ b S i = s by
    simpa using congrArg ((classOfReprIso T).inv ≫ ·) (H ((classOfReprIso T).hom ≫ t))
  intro s
  simp only [Preadditive.comp_sum]
  rw [Finset.sum_eq_single (classOf T)]
  · simp only [← Category.assoc, Basis.comp_homDual, Linear.smul_comp, Category.id_comp,
      Basis.sum_repr]
  · -- Morphisms between representatives of distinct classes vanish.
    intro S _ hS
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have := homOrthogonal_repr (D := C) (Ne.symm hS)
    rw [← Category.assoc, Subsingleton.elim (s ≫ (b S).homDual i) 0, zero_comp]
  · simp

variable {D : Type u'} [Category.{v'} D] [Abelian D] [Linear k D] [IsFiniteSemisimpleCategory D]
variable {M : Type*} [AddCommGroup M] [Module k M]

/-- The canonical element of a simple object `S` of `D` and the image `F.obj B` of an object
under an additive functor, computed through the simple constituents of `B`: the sum over a basis
of `S ⟶ F.obj B` equals the sum over the simple classes `T` of `C` and bases of `T ⟶ B` and
`S ⟶ F.obj T` of the composite basis elements and their composite duals. -/
theorem sum_homDual_eq_sum_map_homDual [Fintype (SimpleClasses C)] (F : C ⥤ D) [F.Additive]
    (B : C) (S : D) [Simple S] [FiniteDimensional k (S ⟶ S)]
    {κ : Type*} [Fintype κ] [DecidableEq κ] (c : Basis κ k (S ⟶ F.obj B))
    {ι : SimpleClasses C → Type*} [∀ T, Fintype (ι T)] [∀ T, DecidableEq (ι T)]
    (b : ∀ T : SimpleClasses C, Basis (ι T) k (T.repr ⟶ B))
    {κ' : SimpleClasses C → Type*} [∀ T, Fintype (κ' T)] [∀ T, DecidableEq (κ' T)]
    (a : ∀ T : SimpleClasses C, Basis (κ' T) k (S ⟶ F.obj T.repr))
    (β : (F.obj B ⟶ S) →ₗ[k] (S ⟶ F.obj B) →ₗ[k] M) :
    ∑ i, β (c.homDual i) (c i) =
      ∑ T, ∑ l, ∑ j, β (F.map ((b T).homDual l) ≫ (a T).homDual j) (a T j ≫ F.map (b T l)) := by
  -- Insert the completeness relation for `B` after each basis element of `S ⟶ F.obj B`.
  have h1 : ∀ i, c i = ∑ T, ∑ l, c i ≫ F.map ((b T).homDual l) ≫ F.map (b T l) := fun i ↦ by
    simp_rw [← F.map_comp, ← Preadditive.comp_sum, ← F.map_sum, sum_sum_homDual_comp_eq_id,
      F.map_id, Category.comp_id]
  conv_lhs => enter [2, i]; rw [h1 i]
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  -- Move `F.map ((b T).homDual l)` onto the dual basis by naturality of the canonical element.
  simpa only [LinearMap.compl₂_apply, Linear.rightComp_apply, Category.assoc] using
    c.sum_homDual_comp (a T) (F.map ((b T).homDual l))
      (β.compl₂ (Linear.rightComp k S (F.map (b T l))))

end TauCeti
