/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Abelian
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Monoidal
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Morphism
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.TensorProduct
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Trivial
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Coefficient spaces of finite-dimensional comodules

For a finite-dimensional right comodule `M` over a coalgebra `C` over a field `K`, write
`C(M) ⊆ C` for its space of matrix coefficients,
`TauCeti.Comodule.matrixCoefficientSubmodule`. This file records how `C(M)` interacts with the
categorical structure of `FGComoduleCat K C`:

* quotients and subobjects of `M` have no coefficients outside `C(M)`: `C(N) ≤ C(M)` for an
  epimorphism `M ⟶ N`, and `C(N) ≤ C(M)` for a monomorphism `N ⟶ M` over a field;
* the coefficients of a finite biproduct are the supremum of the coefficients of its summands;
* over a bialgebra, the coefficients of `M ⊗ N` are the products of those of `M` and `N`, and the
  coefficients of the tensor unit are the scalars.

The main result is the converse of the first item: if `C(M) ≤ ⨆ k, C(F k)` for a family `F`,
then `M` is a quotient of a subobject of a finite direct sum of members of `F`. As `C(M)` is
finite-dimensional, finitely many members of `F` carry it. The proof embeds `M` into finitely
many copies of the finite regular subcomodule `D` spanned by their coefficients, using the
coefficient maps of a dual basis of `M`, and writes `D` as a quotient of a finite direct sum of
these members, using the coefficient maps of their dual bases. In particular the finite-sum and
subquotient hull of one comodule `W` consists exactly of the comodules with coefficients in
`C(W)`.

## Main declarations

* `TauCeti.FGComoduleCat.matrixCoefficientSubmodule_le_of_epi`,
  `TauCeti.FGComoduleCat.matrixCoefficientSubmodule_le_of_mono`,
  `TauCeti.FGComoduleCat.matrixCoefficientSubmodule_eq_of_iso`: functoriality of `C(-)`.
* `TauCeti.FGComoduleCat.matrixCoefficientSubmodule_biproduct`: `C(⨁ F) = ⨆ j, C(F j)`.
* `TauCeti.FGComoduleCat.exists_mono_biproduct_of_matrixCoefficientSubmodule_le`: a comodule
  embeds into copies of a finite regular subcomodule containing its coefficients.
* `TauCeti.FGComoduleCat.exists_epi_biproduct_of_toSubmodule_eq_iSup`: the regular subcomodule
  spanned by the coefficients of a finite family is a quotient of a finite sum of its members.
* `TauCeti.FGComoduleCat.matrixCoefficientSubmodule_le_iSup_iff_exists_mono_epi` and
  `TauCeti.FGComoduleCat.matrixCoefficientSubmodule_le_iff_exists_mono_epi`: `C(M) ≤ ⨆ k, C(F k)`
  exactly when `M` is a subquotient of a finite direct sum of members of `F`; for one comodule
  `W`, `C(M) ≤ C(W)` exactly when `M` is a subquotient of a finite direct sum of copies of `W`.
* `TauCeti.FGComoduleCat.matrixCoefficientSubmodule_tensorObj`: `C(M ⊗ N) = C(M) * C(N)`.
* `TauCeti.FGComoduleCat.matrixCoefficientSubmodule_tensorUnit`: `C(𝟙_) = K • 1`.
* `TauCeti.FGComoduleCat.mul_matrixCoefficientSubmodule_tensorPow`: coefficients of tensor
  powers multiply.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, proof of Proposition 2.20 and
  Corollary 2.22.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.5.
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace TauCeti.FGComoduleCat

universe u v w

section Ring

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- A quotient of a finite comodule has fewer matrix coefficients. -/
theorem matrixCoefficientSubmodule_le_of_epi {M N : FGComoduleCat.{u, v, w} R C} (f : M ⟶ N)
    [Epi f] :
    Comodule.matrixCoefficientSubmodule (R := R) (C := C) (M := N) ≤
      Comodule.matrixCoefficientSubmodule (R := R) (C := C) (M := M) :=
  Comodule.matrixCoefficientSubmodule_le_of_surjective f.hom (surjective_of_epi f)

/-- Isomorphic finite comodules have the same matrix coefficients. -/
theorem matrixCoefficientSubmodule_eq_of_iso {M N : FGComoduleCat.{u, v, w} R C} (e : M ≅ N) :
    Comodule.matrixCoefficientSubmodule (R := R) (C := C) (M := M) =
      Comodule.matrixCoefficientSubmodule (R := R) (C := C) (M := N) :=
  le_antisymm (matrixCoefficientSubmodule_le_of_epi e.inv)
    (matrixCoefficientSubmodule_le_of_epi e.hom)

/-- Every summand of a finite biproduct of finite comodules has its matrix coefficients among
those of the biproduct. -/
theorem le_matrixCoefficientSubmodule_biproduct {ι : Type} [Finite ι]
    (F : ι → FGComoduleCat.{u, v, w} R C) (j : ι) :
    Comodule.matrixCoefficientSubmodule (R := R) (C := C) (M := F j) ≤
      Comodule.matrixCoefficientSubmodule (R := R) (C := C) (M := ↥(⨁ F)) :=
  matrixCoefficientSubmodule_le_of_epi (biproduct.π F j)

/-- The matrix coefficients of a finite biproduct of finite comodules are spanned by those of
its summands. -/
@[simp]
theorem matrixCoefficientSubmodule_biproduct {ι : Type} [Finite ι]
    (F : ι → FGComoduleCat.{u, v, w} R C) :
    Comodule.matrixCoefficientSubmodule (R := R) (C := C) (M := ↥(⨁ F)) =
      ⨆ j, Comodule.matrixCoefficientSubmodule (R := R) (C := C) (M := F j) := by
  let := Fintype.ofFinite ι
  refine le_antisymm (Comodule.matrixCoefficientSubmodule_le fun φ z ↦ ?_)
    (iSup_le (le_matrixCoefficientSubmodule_biproduct F))
  -- Decompose `z` along the biproduct, then pull `φ` back to each summand.
  have hz : z = ∑ j, biproduct.ι F j (biproduct.π F j z) := by
    exact (ConcreteCategory.congr_hom (biproduct.total (f := F)) z).symm.trans
      (FGComoduleCat.sum_apply _ _ z)
  rw [hz, ← Comodule.matrixCoefficientLinear_apply, map_sum]
  refine Submodule.sum_mem _ fun j _ ↦ Submodule.mem_iSup_of_mem j ?_
  rw [Comodule.matrixCoefficientLinear_apply]
  exact (Comodule.matrixCoefficient_map (biproduct.ι F j).hom φ _).symm ▸
    Comodule.matrixCoefficient_mem_submodule (R := R) (C := C) _ _

end Ring

section Field

variable {K : Type u} [Field K]
variable {C : Type v} [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- A subobject of a finite-dimensional comodule has fewer matrix coefficients: every functional
on the subobject extends to the ambient comodule. -/
theorem matrixCoefficientSubmodule_le_of_mono {M N : FGComoduleCat.{u, v, w} K C} (f : M ⟶ N)
    [Mono f] :
    Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := M) ≤
      Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := N) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f.hom.toLinearMap
    (LinearMap.ker_eq_bot.2 (injective_of_mono f))
  refine Comodule.matrixCoefficientSubmodule_le fun φ m ↦ ?_
  have h : Comodule.matrixCoefficient (R := K) (C := C) φ m =
      Comodule.matrixCoefficient (R := K) (C := C) (φ ∘ₗ g) (f.hom m) := by
    rw [Comodule.matrixCoefficient_map]
    congr 1
    ext x
    exact congrArg φ (LinearMap.congr_fun hg x).symm
  rw [h]
  exact Comodule.matrixCoefficient_mem_submodule (R := K) (C := C) _ _

/-- A finite comodule embeds into finitely many copies of any finite regular subcomodule `D`
containing its matrix coefficients. The embedding is given by the coefficient maps of a dual
basis; it is injective because the counit recovers each functional from its coefficient map. -/
theorem exists_mono_biproduct_of_matrixCoefficientSubmodule_le (M : FGComoduleCat.{u, v, v} K C)
    (D : Subcomodule K C C) [Module.Finite K D]
    (h : Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := M) ≤ D.toSubmodule) :
    ∃ (ι : Type) (_ : Finite ι) (f : M ⟶ ⨁ fun _ : ι ↦ of (R := K) (C := C) D), Mono f := by
  classical
  let n := Module.finrank K M
  let b := Module.finBasis K M
  let c (i : Fin n) : M ⟶ of (R := K) (C := C) D :=
    ObjectProperty.homMk (ComoduleCat.ofHom (R := K) (C := C)
      ((Comodule.matrixCoefficientHom (C := C) (b.coord i)).codRestrict D fun x ↦ by
        rw [← Subcomodule.mem_toSubmodule, Comodule.matrixCoefficientHom_apply]
        exact h (Comodule.matrixCoefficient_mem_submodule (R := K) (C := C) _ x)))
  have hc (i) (x : M) : ((c i x : ↥D) : C) = Comodule.matrixCoefficient (R := K) (C := C)
      (b.coord i) x :=
    (Comodule.Hom.codRestrict_apply _ _ _ x).trans (Comodule.matrixCoefficientHom_apply _ x)
  let f : M ⟶ ⨁ fun _ : Fin n ↦ of (R := K) (C := C) D := biproduct.lift c
  refine ⟨Fin n, inferInstance, f, ConcreteCategory.mono_of_injective f fun x y hxy ↦
    b.ext_elem fun i ↦ ?_⟩
  have hi : c i x = c i y := by
    have := congrArg (biproduct.π (fun _ : Fin n ↦ of (R := K) (C := C) D) i) hxy
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, biproduct.lift_π] at this
  have := congrArg (fun z : ↥D ↦ Coalgebra.counit (R := K) (A := C) (z : C)) hi
  simpa only [hc, Comodule.counit_matrixCoefficient, Module.Basis.coord_apply] using this

/-- A finite regular subcomodule `D` spanned by the matrix coefficients of a finite family `F`
of finite comodules is a quotient of a finite direct sum of members of `F`. The quotient map is
given by the coefficient maps of dual bases of the members of `F`. -/
theorem exists_epi_biproduct_of_toSubmodule_eq_iSup {κ : Type} [Finite κ]
    (D : Subcomodule K C C) [Module.Finite K D] {F : κ → FGComoduleCat.{u, v, v} K C}
    (hD : D.toSubmodule =
      ⨆ k, Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := F k)) :
    ∃ (ι : Type) (_ : Finite ι) (g : ι → κ) (f : (⨁ fun j ↦ F (g j)) ⟶ of (R := K) (C := C) D),
      Epi f := by
  classical
  let := Fintype.ofFinite κ
  let n (k : κ) := Module.finrank K (F k)
  let b (k : κ) := Module.finBasis K (F k)
  let c (q : Σ k, Fin (n k)) : F q.1 ⟶ of (R := K) (C := C) D :=
    ObjectProperty.homMk (ComoduleCat.ofHom (R := K) (C := C)
      ((Comodule.matrixCoefficientHom (C := C) ((b q.1).coord q.2)).codRestrict D fun w ↦ by
        rw [← Subcomodule.mem_toSubmodule, hD, Comodule.matrixCoefficientHom_apply]
        exact Submodule.mem_iSup_of_mem q.1
          (Comodule.matrixCoefficient_mem_submodule (R := K) (C := C) _ w)))
  have hc (q) (w : F q.1) : ((c q w : ↥D) : C) =
      Comodule.matrixCoefficient (R := K) (C := C) ((b q.1).coord q.2) w :=
    (Comodule.Hom.codRestrict_apply _ _ _ w).trans (Comodule.matrixCoefficientHom_apply _ w)
  let f : (⨁ fun q : Σ k, Fin (n k) ↦ F q.1) ⟶ of (R := K) (C := C) D := biproduct.desc c
  have hf (q) (w : F q.1) : f (biproduct.ι (fun q : Σ k, Fin (n k) ↦ F q.1) q w) = c q w := by
    rw [← ConcreteCategory.comp_apply, biproduct.ι_desc]
  -- Every coefficient of a member of `F` is in the range of `f`.
  let L := D.toSubmodule.subtype ∘ₗ f.hom.toLinearMap
  have hL : (⨆ k, Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := F k)) ≤
      LinearMap.range L := by
    refine iSup_le fun k ↦ Comodule.matrixCoefficientSubmodule_le fun φ w ↦
      ⟨∑ j, biproduct.ι (fun q : Σ k, Fin (n k) ↦ F q.1) ⟨k, j⟩ (φ (b k j) • w), ?_⟩
    rw [map_sum]
    conv_rhs => rw [← (b k).sum_dual_apply_smul_coord φ]
    rw [← Comodule.matrixCoefficientBilinear_apply_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    -- `L` is `f` followed by the inclusion of `D`; unfold it on this summand.
    change ((f (biproduct.ι (fun q : Σ k, Fin (n k) ↦ F q.1) ⟨k, j⟩ (φ (b k j) • w)) : ↥D) :
      C) = _
    rw [hf, hc, map_smul, LinearMap.smul_apply, Comodule.matrixCoefficientBilinear_apply_apply,
      Comodule.matrixCoefficient_smul]
  refine ⟨Σ k, Fin (n k), inferInstance, fun q ↦ q.1, f,
    ConcreteCategory.epi_of_surjective f fun y ↦ ?_⟩
  have hy : (y : C) ∈ D.toSubmodule := Subcomodule.mem_toSubmodule.2 y.property
  rw [hD] at hy
  obtain ⟨z, hz⟩ := hL hy
  exact ⟨z, Subtype.ext hz⟩

/-- **Comodules with coefficients in `⨆ k, C(F k)` are subquotients of sums of the `F k`.** If
the matrix coefficients of `M` lie among those of a family `F`, then `M` is a quotient of a
subobject of a finite direct sum of members of `F`.

As `C(M)` is finite-dimensional, finitely many members of `F` carry it. Let `D ⊆ C` be the finite
regular subcomodule spanned by the coefficients of these `F k`. Then `M` embeds into finitely
many copies of `D` (`exists_mono_biproduct_of_matrixCoefficientSubmodule_le`), and `D` is a
quotient of a finite direct sum of members of `F`
(`exists_epi_biproduct_of_toSubmodule_eq_iSup`). The pullback of these two maps is the required
subobject. -/
theorem exists_mono_epi_of_matrixCoefficientSubmodule_le_iSup {κ : Type}
    {M : FGComoduleCat.{u, v, v} K C} {F : κ → FGComoduleCat.{u, v, v} K C}
    (h : Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := M) ≤
      ⨆ k, Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := F k)) :
    ∃ (ι : Type) (_ : Finite ι) (g : ι → κ) (Z : FGComoduleCat.{u, v, v} K C)
      (i : Z ⟶ ⨁ fun j ↦ F (g j)) (p : Z ⟶ M), Mono i ∧ Epi p := by
  obtain ⟨s, hs⟩ := ((Submodule.fg_iff_compact _).1 (Module.Finite.iff_fg.1 inferInstance)
    ).exists_finset_of_le_iSup _ h
  let D : Subcomodule K C C := ⨆ k : s,
    (Comodule.matrixCoefficientSubcoalgebra (R := K) (C := C) (M := F k)).toRegularSubcomodule
  have hD : D.toSubmodule =
      ⨆ k : s, Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := F k) := by
    simp only [D, Subcomodule.iSup_toSubmodule, Subcoalgebra.toRegularSubcomodule_toSubmodule,
      Comodule.matrixCoefficientSubcoalgebra_toSubmodule]
  have : Module.Finite K D := by
    -- The carrier of `D` is that of its underlying submodule.
    change Module.Finite K D.toSubmodule
    rw [hD]
    infer_instance
  obtain ⟨ι, _, g, e, _⟩ := exists_epi_biproduct_of_toSubmodule_eq_iSup D hD
  obtain ⟨κ', _, Φ, _⟩ := exists_mono_biproduct_of_matrixCoefficientSubmodule_le M D <|
    hs.trans <| hD.ge.trans' <| iSup₂_le fun k hk ↦ le_iSup_of_le ⟨k, hk⟩ le_rfl
  -- Combine copies of the quotient map `e` into one epimorphism onto the copies of `D`.
  let E : (⨁ fun p : Σ _ : κ', ι ↦ F (g p.2)) ⟶ ⨁ fun _ : κ' ↦ of (R := K) (C := C) D :=
    (biproductBiproductIso (fun _ : κ' ↦ ι) (fun _ j ↦ F (g j))).inv ≫
      biproduct.map fun _ : κ' ↦ e
  exact ⟨Σ _ : κ', ι, inferInstance, fun p ↦ (g p.2).val, pullback E Φ, pullback.fst E Φ,
    pullback.snd E Φ, inferInstance, inferInstance⟩

/-- **Subquotients of finite sums are cut out by coefficients.** A finite comodule `M` is a
quotient of a subobject of a finite direct sum of members of a family `F` exactly when its
matrix coefficients lie among those of the members of `F`. -/
theorem matrixCoefficientSubmodule_le_iSup_iff_exists_mono_epi {κ : Type}
    {M : FGComoduleCat.{u, v, v} K C} {F : κ → FGComoduleCat.{u, v, v} K C} :
    Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := M) ≤
        ⨆ k, Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := F k) ↔
      ∃ (ι : Type) (_ : Finite ι) (g : ι → κ) (Z : FGComoduleCat.{u, v, v} K C)
        (i : Z ⟶ ⨁ fun j ↦ F (g j)) (p : Z ⟶ M), Mono i ∧ Epi p := by
  refine ⟨exists_mono_epi_of_matrixCoefficientSubmodule_le_iSup, ?_⟩
  rintro ⟨ι, _, g, Z, i, p, _, _⟩
  calc Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := M)
      _ ≤ Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := Z) :=
        matrixCoefficientSubmodule_le_of_epi p
      _ ≤ Comodule.matrixCoefficientSubmodule (R := K) (C := C)
          (M := ↥(⨁ fun j ↦ F (g j))) :=
        matrixCoefficientSubmodule_le_of_mono i
      _ ≤ ⨆ k, Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := F k) := by
        rw [matrixCoefficientSubmodule_biproduct]
        exact iSup_le fun j ↦ le_iSup (fun k ↦
          Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := F k)) (g j)

/-- **The finite-sum and subquotient hull of `W` is cut out by coefficients.** A finite
comodule `M` is a quotient of a subobject of a finite direct sum of copies of `W` exactly when
its matrix coefficients lie among those of `W`. -/
theorem matrixCoefficientSubmodule_le_iff_exists_mono_epi {M W : FGComoduleCat.{u, v, v} K C} :
    Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := M) ≤
        Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := W) ↔
      ∃ (ι : Type) (_ : Finite ι) (Z : FGComoduleCat.{u, v, v} K C)
        (i : Z ⟶ ⨁ fun _ : ι ↦ W) (p : Z ⟶ M), Mono i ∧ Epi p := by
  have h := matrixCoefficientSubmodule_le_iSup_iff_exists_mono_epi (κ := Unit) (M := M)
    (F := fun _ ↦ W)
  rw [iSup_const] at h
  rw [h]
  exact ⟨fun ⟨ι, hι, _, Z, i, p, hip⟩ ↦ ⟨ι, hι, Z, i, p, hip⟩,
    fun ⟨ι, hι, Z, i, p, hip⟩ ↦ ⟨ι, hι, fun _ ↦ (), Z, i, p, hip⟩⟩

end Field

section Bialgebra

variable {R : Type u} [CommSemiring R]
variable {C : Type v} [Semiring C] [Bialgebra R C]

attribute [local instance] Comodule.tensor Comodule.trivial

/-- The matrix coefficients of a tensor product of finite comodules, the first of them
projective, are the products of the coefficients of the two factors. -/
@[simp]
theorem matrixCoefficientSubmodule_tensorObj (M N : FGComoduleCat.{u, v, u} R C)
    [Module.Projective R M] :
    Comodule.matrixCoefficientSubmodule (R := R) (C := C) (M := ↥(M ⊗ N)) =
      Comodule.matrixCoefficientSubmodule (R := R) (C := C) (M := M) *
        Comodule.matrixCoefficientSubmodule (R := R) (C := C) (M := N) :=
  Comodule.matrixCoefficientSubmodule_tensor (R := R) (C := C) (M := M) (N := N)

/-- The matrix coefficients of the tensor unit are the scalar multiples of `1`.

This is the bundled form of
`Comodule.trivial_rankOne_matrixCoefficientSubmodule_eq_span_singleton_one`. It is not a `simp`
lemma because `simp` already proves it from the group-like coefficient lemmas. -/
theorem matrixCoefficientSubmodule_tensorUnit :
    Comodule.matrixCoefficientSubmodule (R := R) (C := C)
        (M := ↥(𝟙_ (FGComoduleCat.{u, v, u} R C))) =
      Submodule.span R {1} :=
  Comodule.trivial_rankOne_matrixCoefficientSubmodule_eq_span_singleton_one (R := R) (C := C)

end Bialgebra

section FieldBialgebra

variable {K : Type u} [Field K]
variable {C : Type v} [Semiring C] [Bialgebra K C]

/-- The matrix coefficients of two tensor powers of a finite-dimensional comodule multiply into
the coefficients of the tensor power of the summed degree. -/
theorem mul_matrixCoefficientSubmodule_tensorPow (X : FGComoduleCat.{u, v, u} K C) (m n : ℕ) :
    Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := ↥(tensorPow X m)) *
        Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := ↥(tensorPow X n)) =
      Comodule.matrixCoefficientSubmodule (R := K) (C := C) (M := ↥(tensorPow X (n + m))) := by
  rw [← matrixCoefficientSubmodule_tensorObj,
    matrixCoefficientSubmodule_eq_of_iso (tensorPowAddIso X m n)]

end FieldBialgebra

end TauCeti.FGComoduleCat
