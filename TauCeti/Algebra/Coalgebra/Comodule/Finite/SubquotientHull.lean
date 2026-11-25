/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.MatrixCoefficient
public import TauCeti.Algebra.HopfAlgebra.Subalgebra
public import TauCeti.CategoryTheory.Monoidal.SumOfUnits
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Regular
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Subcoalgebra
import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
import TauCeti.Algebra.Coalgebra.Subcoalgebra.Lattice

/-!
# Tensor-closed hulls of finite comodules

Let `H` be a bialgebra over a field `K` and `X` a finite-dimensional comodule. Its finite-sum and
subquotient hull `⟨X⟩ = TauCeti.subquotientHull X` consists exactly of the finite comodules whose
matrix coefficients lie in the coefficient space `C(X) ⊆ H` of `X`. As the coefficients of a
tensor product are the products of the coefficients of the factors, tensor-closedness of `⟨X⟩` is
a property of the subspace `C(X)`:

* `⟨X⟩` is closed under tensor products exactly when `C(X) * C(X) ≤ C(X)`, and it contains the
  unit exactly when `1 ∈ C(X)`;
* `X` is a sum of units exactly when `C(X)` lies in the scalars `K ∙ 1`; in particular the
  subquotients of finite sums of units are again sums of units.

For a commutative Hopf algebra `H`, a coefficient space closed under multiplication spans, with
`1`, a finite-dimensional subbialgebra, which is then a Hopf subalgebra. Conversely a
finite-dimensional Hopf subalgebra is the coefficient space of its own regular comodule. So some
finite comodule other than a sum of units has a tensor-closed hull exactly when `H` has a
finite-dimensional Hopf subalgebra other than `⊥`. In terms of the affine group `G = Spec H`: a
nontrivial representation whose hull is tensor-closed is the same as a nontrivial finite quotient
of `G`. This is the representation-theoretic half of the connectedness criterion for neutral
Tannakian categories.

## Main declarations

* `TauCeti.FGComoduleCat.subquotientHull_iff_matrixCoefficientSubmodule_le`: `M ∈ ⟨W⟩` exactly
  when `C(M) ≤ C(W)`.
* `TauCeti.FGComoduleCat.tensorLE_subquotientHull_iff`: `⟨X⟩` is closed under tensor products
  exactly when `C(X) * C(X) ≤ C(X)`.
* `TauCeti.FGComoduleCat.containsUnit_subquotientHull_iff`,
  `TauCeti.FGComoduleCat.isMonoidal_subquotientHull_iff`: the unit and monoidal variants.
* `TauCeti.FGComoduleCat.isSumOfUnits_iff_matrixCoefficientSubmodule_le`: `X` is a sum of units
  exactly when `C(X) ≤ K ∙ 1`.
* `TauCeti.FGComoduleCat.subquotientHull_tensorUnit_iff_isSumOfUnits`: the hull of the unit
  consists of the sums of units.
* `TauCeti.FGComoduleCat.exists_not_isSumOfUnits_tensorLE_subquotientHull_iff`: a finite comodule
  other than a sum of units with tensor-closed hull exists exactly when `H` has a
  finite-dimensional Hopf subalgebra other than `⊥`.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, Proposition 2.20 and Corollary 2.22 with
  their proofs.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§3.3–3.5 and 6.7.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti.FGComoduleCat

universe u v

section Coalgebra

variable {K : Type u} [Field K] {C : Type v} [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- **The hull of `W` is cut out by coefficients.** A finite comodule lies in the finite-sum and
subquotient hull of `W` exactly when its matrix coefficients lie among those of `W`. -/
theorem subquotientHull_iff_matrixCoefficientSubmodule_le {W M : FGComoduleCat.{u, v, v} K C} :
    subquotientHull W M ↔
      Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := M) ≤
        Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := W) :=
  subquotientHull_iff.trans matrixCoefficientSubmodule_le_iff_exists_mono_epi.symm

end Coalgebra

section Bialgebra

variable {K : Type u} [Field K] {H : Type u} [Ring H] [Bialgebra K H]
  {X : FGComoduleCat.{u, u, u} K H}

/-- **Tensor-closed hulls.** The finite-sum and subquotient hull of a finite comodule `X` is
closed under tensor products exactly when the matrix coefficients of `X` are closed under
multiplication. -/
theorem tensorLE_subquotientHull_iff :
    (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X) ↔
      Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X) *
          Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X) ≤
        Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X) := by
  refine ⟨fun _ ↦ ?_, fun h ↦ ⟨fun Y Z hY hZ ↦ ?_⟩⟩
  · have hXX : subquotientHull X (X ⊗ X) :=
      ObjectProperty.prop_tensor (Q := subquotientHull X) subquotientHull_self
        subquotientHull_self
    rwa [subquotientHull_iff_matrixCoefficientSubmodule_le,
      matrixCoefficientSubmodule_tensorObj] at hXX
  · rw [subquotientHull_iff_matrixCoefficientSubmodule_le] at hY hZ ⊢
    rw [matrixCoefficientSubmodule_tensorObj]
    exact (mul_le_mul' hY hZ).trans h

/-- The finite-sum and subquotient hull of a finite comodule `X` contains the tensor unit
exactly when `1` is a matrix coefficient of `X`. -/
theorem containsUnit_subquotientHull_iff :
    (subquotientHull X).ContainsUnit ↔
      (1 : H) ∈ Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X) := by
  rw [← Submodule.span_singleton_le_iff_mem, ← matrixCoefficientSubmodule_tensorUnit,
    ← subquotientHull_iff_matrixCoefficientSubmodule_le]
  exact ⟨fun h ↦ h.prop_unit, fun h ↦ ⟨h⟩⟩

/-- The finite-sum and subquotient hull of a finite comodule `X` is a monoidal subcategory
exactly when the matrix coefficients of `X` are closed under multiplication and contain `1`. -/
theorem isMonoidal_subquotientHull_iff :
    (subquotientHull X).IsMonoidal ↔
      Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X) *
          Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X) ≤
        Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X) ∧
      (1 : H) ∈ Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X) := by
  rw [← tensorLE_subquotientHull_iff, ← containsUnit_subquotientHull_iff]
  exact ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ { }⟩

end Bialgebra

section SumOfUnits

variable {K : Type u} [Field K] {H : Type u} [Ring H] [Bialgebra K H]
  {X : FGComoduleCat.{u, u, u} K H}

attribute [local instance] Comodule.trivial

/-- A finite comodule with trivial coaction `x ↦ x ⊗ 1` is a sum of units: a basis `(bᵢ)` gives
maps `𝟙_ ⟶ X`, `r ↦ r • bᵢ`, and the coordinate maps `X ⟶ 𝟙_` of the basis, which form a
biproduct bicone. -/
private theorem isSumOfUnits_of_coact_eq_tmul_one
    (h : ∀ x : X, Comodule.coact (R := K) (C := H) (M := X) x = x ⊗ₜ[K] (1 : H)) :
    IsSumOfUnits X := by
  classical
  let b := Module.finBasis K X
  let ι (i : Fin (Module.finrank K X)) : 𝟙_ (FGComoduleCat.{u, u, u} K H) ⟶ X :=
    ObjectProperty.homMk (ComoduleCat.ofHom (R := K) (C := H)
      { toLinearMap := LinearMap.toSpanSingleton K X (b i)
        map_coact := LinearMap.ext_ring (by simp [h]) })
  let π (i : Fin (Module.finrank K X)) : X ⟶ 𝟙_ (FGComoduleCat.{u, u, u} K H) :=
    ObjectProperty.homMk (ComoduleCat.ofHom (R := K) (C := H)
      { toLinearMap := b.coord i
        map_coact := by ext x; simp [h] })
  have hι (i) (r : K) : ι i r = r • b i := rfl
  have hπ (i) (x : X) : π i x = b.coord i x := rfl
  let c : Bicone fun _ : Fin (Module.finrank K X) ↦ 𝟙_ (FGComoduleCat.{u, u, u} K H) :=
    { pt := X
      π := π
      ι := ι
      ι_π := fun j j' ↦ by
        refine ConcreteCategory.hom_ext _ _ fun r ↦ ?_
        rw [ConcreteCategory.comp_apply, hπ, hι, map_smul, Module.Basis.coord_apply,
          b.repr_self]
        split_ifs with hjj
        · subst hjj
          simp
        · simp [hjj] }
  -- Evaluation at a vector is additive in the morphism.
  let ev (x : X) : (X ⟶ X) →+ X :=
    { toFun f := f x
      map_zero' := rfl
      map_add' _ _ := rfl }
  have htotal : ∑ j, c.π j ≫ c.ι j = 𝟙 c.pt := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    calc (∑ j, c.π j ≫ c.ι j) x = ∑ j, (c.π j ≫ c.ι j) x := map_sum (ev x) _ _
      _ = x := by simp [c, hπ, hι]
  exact .mk (biproduct.uniqueUpToIso _ (isBilimitOfTotal c htotal))

/-- **Sums of units are the comodules with scalar coefficients.** A finite comodule is a sum of
units exactly when all its matrix coefficients are scalar multiples of `1`. -/
theorem isSumOfUnits_iff_matrixCoefficientSubmodule_le :
    IsSumOfUnits X ↔ Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X) ≤ K ∙ 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ isSumOfUnits_of_coact_eq_tmul_one ?_⟩
  · obtain ⟨ι, _, ⟨e⟩⟩ := isSumOfUnits_iff.1 h
    rw [matrixCoefficientSubmodule_eq_of_iso e, matrixCoefficientSubmodule_biproduct]
    exact iSup_le fun _ ↦ matrixCoefficientSubmodule_tensorUnit.le
  · simpa using (Comodule.matrixCoefficientSubmodule_le_span_singleton_iff
      (R := K) (C := H) (M := X) (1 : GroupLike K H)).1 (by simpa using h)

/-- **Subquotients of sums of units are sums of units.** The finite-sum and subquotient hull of
the tensor unit consists exactly of the sums of units. -/
theorem subquotientHull_tensorUnit_iff_isSumOfUnits :
    subquotientHull (𝟙_ (FGComoduleCat.{u, u, u} K H)) X ↔ IsSumOfUnits X := by
  rw [subquotientHull_iff_matrixCoefficientSubmodule_le, matrixCoefficientSubmodule_tensorUnit,
    isSumOfUnits_iff_matrixCoefficientSubmodule_le]

end SumOfUnits

section HopfAlgebra

variable {K : Type u} [Field K] {H : Type u} [CommRing H] [HopfAlgebra K H]

/-- A finite comodule other than a sum of units whose hull is closed under tensor products
yields a finite-dimensional Hopf subalgebra other than `⊥`: its coefficients together with the
scalars. -/
private theorem exists_isHopfSubalgebra_ne_bot_of_tensorLE {X : FGComoduleCat.{u, u, u} K H}
    (hX : ¬ IsSumOfUnits X)
    (hT : (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X)) :
    ∃ A : Subalgebra K H, A.IsHopfSubalgebra ∧ FiniteDimensional K A ∧ A ≠ ⊥ := by
  let P := Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X)
  have hP : P * P ≤ P := tensorLE_subquotientHull_iff.1 hT
  -- The scalars and the coefficients of `X` span a subcoalgebra closed under multiplication.
  let D : Subcoalgebra K H := Subcoalgebra.groupLikeSpan (1 : GroupLike K H) ⊔
    Comodule.matrixCoefficientSubcoalgebra (R := K) (C := H) (M := X)
  have hD : D.toSubmodule = 1 ⊔ P := by
    simp [D, P, Subcoalgebra.groupLikeSpan_toSubmodule, Submodule.one_eq_span]
  have hDmul : D.toSubmodule * D.toSubmodule ≤ D.toSubmodule := by
    rw [hD, Submodule.sup_mul, Submodule.mul_sup, Submodule.mul_sup, one_mul, mul_one, one_mul]
    exact sup_le (sup_le le_sup_left le_sup_right) (sup_le le_sup_right (hP.trans le_sup_right))
  let A : Subalgebra K H := D.toSubmodule.toSubalgebra
    (hD ▸ Submodule.one_le.1 le_sup_left)
    fun _ _ hx hy ↦ hDmul (Submodule.mul_mem_mul hx hy)
  have : FiniteDimensional K A := inferInstanceAs (Module.Finite K D.toSubmodule)
  refine ⟨A, Subalgebra.IsHopfSubalgebra.of_finiteDimensional fun _ hx ↦ D.comul_mem hx,
    inferInstance, fun hA ↦ hX ?_⟩
  rw [isSumOfUnits_iff_matrixCoefficientSubmodule_le, ← Submodule.one_eq_span,
    ← Algebra.toSubmodule_bot, ← hA, Submodule.toSubalgebra_toSubmodule, hD]
  exact le_sup_right

/-- A finite-dimensional Hopf subalgebra other than `⊥` is the coefficient space of its own
regular comodule, which is then not a sum of units and has a tensor-closed hull. -/
private theorem exists_not_isSumOfUnits_tensorLE_of_isHopfSubalgebra {A : Subalgebra K H}
    (hA : A.IsHopfSubalgebra) [FiniteDimensional K A] (hbot : A ≠ ⊥) :
    ∃ X : FGComoduleCat.{u, u, u} K H, ¬ IsSumOfUnits X ∧
      (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X) := by
  have : Module.Finite K hA.toSubcoalgebra.toRegularSubcomodule :=
    inferInstanceAs (Module.Finite K A)
  let X : FGComoduleCat.{u, u, u} K H := of (R := K) (C := H) hA.toSubcoalgebra.toRegularSubcomodule
  have hX : Comodule.matrixCoefficientSubmodule (R := K) (C := H) (M := X) =
      Subalgebra.toSubmodule A :=
    Subcoalgebra.matrixCoefficientSubmodule_toRegularSubcomodule hA.toSubcoalgebra
  refine ⟨X, fun h ↦ hbot ?_, tensorLE_subquotientHull_iff.2 ?_⟩
  · rw [isSumOfUnits_iff_matrixCoefficientSubmodule_le, hX, ← Submodule.one_eq_span,
      ← Algebra.toSubmodule_bot, Subalgebra.toSubmodule.le_iff_le] at h
    exact le_bot_iff.1 h
  · rw [hX]
    exact Submodule.mul_le.2 fun _ hx _ hy ↦ A.mul_mem hx hy

/-- **Tensor-closed hulls and finite Hopf subalgebras.** For a commutative Hopf algebra `H` over a
field, some finite comodule other than a sum of units has a finite-sum and subquotient hull
closed under tensor products exactly when `H` has a finite-dimensional Hopf subalgebra other than
`⊥`. Geometrically: the affine group `Spec H` has a nontrivial finite quotient exactly when some
nontrivial representation generates a tensor-closed hull. -/
theorem exists_not_isSumOfUnits_tensorLE_subquotientHull_iff :
    (∃ X : FGComoduleCat.{u, u, u} K H, ¬ IsSumOfUnits X ∧
        (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X)) ↔
      ∃ A : Subalgebra K H, A.IsHopfSubalgebra ∧ FiniteDimensional K A ∧ A ≠ ⊥ :=
  ⟨fun ⟨_, hX, hT⟩ ↦ exists_isHopfSubalgebra_ne_bot_of_tensorLE hX hT,
    fun ⟨_, hA, _, hbot⟩ ↦ exists_not_isSumOfUnits_tensorLE_of_isHopfSubalgebra hA hbot⟩

end HopfAlgebra

end TauCeti.FGComoduleCat
