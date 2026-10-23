/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Sigma
public import Mathlib.Data.Fintype.Option
public import TauCeti.Algebra.Category.FGModuleCat.Zero
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Rep.OfMulAction

/-!
# Permutation classes in the Grothendieck group of a group algebra

Let `G` be a monoid and `k` a commutative ring. A finite `G`-set `X` gives the permutation
representation `k[X]`, and its `k[G]`-module is finitely generated, so it has a class

```text
permK0 k G X = [k[X]] ∈ G₀(k[G])
```

in the exact Grothendieck group of finitely generated `k[G]`-modules. This file records how that
class depends on `X`: only through the isomorphism class of the `G`-set
(`TauCeti.permK0_congr`), additively in disjoint unions (`TauCeti.permK0_sum`,
`TauCeti.permK0_sigma`, `TauCeti.permK0_sigma_fin`), with the empty set giving `0` and a point
giving the class of the trivial line (`TauCeti.permK0_of_subsingleton`). So an equivariant
bijection between two finite `G`-sets assembled as disjoint unions of coset spaces `G ⧸ S` becomes
a linear relation between the classes `[k[G ⧸ S]]`. For a finite group these are the classes
induced from the trivial lines of the subgroups (`TauCeti.indK0_of_trivial`).

Additivity in disjoint unions comes from the additivity of classes on products of modules
(`TauCeti.exactK0_fgModuleCat_prod`), since the permutation representation on `X ⊕ Y` is the
product of those on `X` and `Y` (`TauCeti.ofMulActionSumEquiv`), and the module of a product
representation is the product of the modules (`Representation.prodAsModuleEquiv`). No
hypothesis on the characteristic of `k` is needed: the relations of `G₀(k[G])` come from all short
exact sequences, including non-split ones, but the relations used here come from split
sequences.

## Main definitions

* `TauCeti.permK0`: the class of the permutation module of a finite `G`-set.

## Main results

* `TauCeti.permK0_eq_of_equiv`: the permutation class is the class of any equivalent
  representation.
* `TauCeti.permK0_congr`: equivariantly equivalent `G`-sets have the same class.
* `TauCeti.permK0_sum`, `TauCeti.permK0_sigma`, `TauCeti.permK0_sigma_fin`: the class is additive
  in disjoint unions.
* `TauCeti.permK0_of_isEmpty`, `TauCeti.permK0_of_subsingleton`: the empty set has class `0`, and a
  point has the class of the trivial line.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §14.1 and
  §16.1, for the Grothendieck group `R_k(G)` and its permutation classes.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

namespace TauCeti

universe u

section Monoid

variable (k : Type u) [CommRing k] {G : Type u} [Monoid G]

variable (G) in
/-- **The permutation class of a finite `G`-set.** The class in `G₀(k[G])` of the `k[G]`-module
of the permutation representation `k[X]`. It is characterized by `TauCeti.permK0_def`. -/
noncomputable def permK0 (X : Type u) [MulAction G X] [Finite X] :
    ExactK0 (finiteModulesExactStructure k[G]) :=
  letI : Module.Finite k[G] (Representation.ofMulAction k G X).asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  ExactK0.of (FGModuleCat.of k[G] (Representation.ofMulAction k G X).asModule)

variable (X Y : Type u) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]

/-- The permutation class is the class of the `k[G]`-module of `Representation.ofMulAction`. -/
theorem permK0_def :
    letI : Module.Finite k[G] (Representation.ofMulAction k G X).asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    permK0 k G X = ExactK0.of (FGModuleCat.of k[G] (Representation.ofMulAction k G X).asModule) :=
  (rfl)

/-- **The permutation class of an equivalent representation.** If `σ` is a representation
equivalent to the permutation representation on `X`, the permutation class of `X` is the class
of the `k[G]`-module of `σ`. -/
theorem permK0_eq_of_equiv {W : Type u} [AddCommGroup W] [Module k W]
    (σ : Representation k G W) (e : (Representation.ofMulAction k G X).Equiv σ) :
    letI : Module.Finite k W := Module.Finite.equiv e.toLinearEquiv
    letI : Module.Finite k[G] σ.asModule := Module.Finite.of_restrictScalars_finite k k[G] _
    permK0 k G X = ExactK0.of (FGModuleCat.of k[G] σ.asModule) := by
  let : Module.Finite k W := Module.Finite.equiv e.toLinearEquiv
  let : Module.Finite k[G] σ.asModule := Module.Finite.of_restrictScalars_finite k k[G] _
  let : Module.Finite k[G] (Representation.ofMulAction k G X).asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  exact ExactK0.of_congr (Representation.asModuleLinearEquivOfEquiv e).toFGModuleCatIso

variable {X Y} in
/-- **Isomorphic `G`-sets have the same permutation class.** -/
theorem permK0_congr (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    permK0 k G X = permK0 k G Y :=
  permK0_eq_of_equiv k X _ (ofMulActionEquivCongr k e he)

/-- **The permutation class is additive in disjoint unions.** -/
@[simp]
theorem permK0_sum : permK0 k G (X ⊕ Y) = permK0 k G X + permK0 k G Y := by
  let : Module.Finite k[G]
      ((Representation.ofMulAction k G X).prod (Representation.ofMulAction k G Y)).asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  let : Module.Finite k[G] (Representation.ofMulAction k G X).asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  let : Module.Finite k[G] (Representation.ofMulAction k G Y).asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  rw [permK0_eq_of_equiv k _ _ (ofMulActionSumEquiv k), permK0_def, permK0_def,
    ← exactK0_fgModuleCat_prod]
  exact ExactK0.of_congr (Representation.prodAsModuleEquiv _ _).toFGModuleCatIso

/-- The permutation class of the empty `G`-set is `0`. -/
@[simp]
theorem permK0_of_isEmpty (X : Type u) [MulAction G X] [IsEmpty X] : permK0 k G X = 0 :=
  ExactK0.of_eq_zero_of_isZero <| FGModuleCat.isZero_of_subsingleton _
    ((Representation.ofMulAction k G X).asModuleEquiv.trans
      (MonoidAlgebra.coeffLinearEquiv k)).toEquiv.subsingleton

/-- **The permutation class of a point.** A one-point `G`-set has the class of the trivial line. -/
@[simp]
theorem permK0_of_subsingleton (X : Type u) [MulAction G X] [Subsingleton X] [Nonempty X] :
    letI : Module.Finite k[G] (Representation.trivial k G k).asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    permK0 k G X = ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule) :=
  permK0_eq_of_equiv k X _ <| .mk
    ((MonoidAlgebra.coeffLinearEquiv k).trans
      (Finsupp.uniqueLinearEquiv k k (Classical.arbitrary X)))
    fun g ↦ by ext x; simp [Representation.ofMulAction_single, Subsingleton.elim (g • x) x]

/-- **The permutation class of a finite disjoint union** is the sum of the classes of the pieces. -/
@[simp]
theorem permK0_sigma {ι : Type u} [Fintype ι] (X : ι → Type u) [∀ i, MulAction G (X i)]
    [∀ i, Finite (X i)] : permK0 k G (Σ i, X i) = ∑ i, permK0 k G (X i) := by
  revert X
  refine Fintype.induction_empty_option (P := fun ι _ ↦ ∀ (X : ι → Type u)
    [∀ i, MulAction G (X i)] [∀ i, Finite (X i)],
      permK0 k G (Σ i, X i) = ∑ i, permK0 k G (X i)) ?_ ?_ ?_ ι
  · intro α β _ e ih X _ _
    let : Fintype α := .ofEquiv β e.symm
    rw [← permK0_congr k (Equiv.sigmaCongrLeft e) fun _ _ ↦ rfl, ih, ← e.sum_comp]
  · intro X _ _
    simp [permK0_of_isEmpty]
  · intro α _ ih X _ _
    -- Split off the summand at `none`.
    let e : (Σ i, X i) ≃ X none ⊕ Σ i, X (some i) :=
      { toFun := fun | ⟨none, x⟩ => .inl x | ⟨some i, x⟩ => .inr ⟨i, x⟩
        invFun := fun | .inl x => ⟨none, x⟩ | .inr ⟨i, x⟩ => ⟨some i, x⟩
        left_inv := by rintro ⟨_ | i, x⟩ <;> rfl
        right_inv := by rintro (x | ⟨i, x⟩) <;> rfl }
    rw [Fintype.sum_option, ← ih, ← permK0_sum, permK0_congr k e ?_]
    rintro g ⟨_ | i, x⟩ <;> rfl

/-- The permutation class of `n` disjoint copies of a `G`-set is `n` times its class. -/
@[simp]
theorem permK0_sigma_fin (n : ℕ) : permK0 k G (Σ _ : Fin n, X) = n • permK0 k G X := by
  rw [permK0_congr k (Equiv.sigmaCongrLeft (Equiv.ulift.{u} (α := Fin n))).symm fun _ _ ↦ rfl,
    permK0_sigma]
  simp

end Monoid

end TauCeti
