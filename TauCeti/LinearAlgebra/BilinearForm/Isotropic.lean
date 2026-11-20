/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis
import Mathlib.LinearAlgebra.Basis.Prod
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Isotropic subspaces of an alternating form and the transitivity of its isometries

A submodule `U` is isotropic for a bilinear form `B` when `U ≤ B.orthogonal U`, and Lagrangian
when `U = B.orthogonal U`. This file shows that for an alternating form every isotropic subspace
lies in a Lagrangian one, and that the isometries of a nondegenerate alternating form on a
finite-dimensional vector space act transitively on the isotropic subspaces of each dimension.
Together with the bound `2 * dim U ≤ dim V`
(`LinearMap.BilinForm.two_mul_finrank_le_finrank_of_le_orthogonal`) and the existence of isotropic
subspaces of every dimension up to half that of `V`, this says that the isotropic subspaces of
dimension `r` form a single nonempty orbit of the symplectic group when `2 * r ≤ dim V`, and that
there are none otherwise.

The argument is Witt's. An isotropic `U` lies in a maximal isotropic subspace `L`, and `L` is
self-orthogonal: a vector of the orthogonal complement of `L` outside `L` could be added to it,
since an alternating form pairs every vector trivially with itself. A basis of `U` extends to a
basis of `L`, which extends to a symplectic basis of `V` with the basis of `L` as its isotropic
half (`LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq`). The linear automorphism
matching two such symplectic bases preserves `B`, since both have Gram matrix `Matrix.J`, and it
carries the first isotropic subspace onto the second. Nothing here divides by two, so all results
hold in characteristic two.

## Main results

* `LinearMap.BilinForm.IsAlt.exists_le_eq_orthogonal`: every isotropic submodule of an alternating
  form on a Noetherian module lies in a self-orthogonal one.
* `LinearMap.BilinForm.eq_orthogonal_iff_two_mul_finrank_eq`: for a nondegenerate form, an
  isotropic subspace is Lagrangian exactly when it has half the ambient dimension.
* `LinearMap.BilinForm.IsAlt.exists_finrank_eq_of_two_mul_le`: there are isotropic subspaces of
  every dimension `r` with `2 * r ≤ dim V`.
* `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_inl_eq`: a basis of an isotropic
  subspace extends to a symplectic basis.
* `LinearMap.BilinForm.IsAlt.exists_isometryEquiv_map_eq`: two isotropic subspaces of the same
  dimension are related by an isometry.

## References

* E. Artin, *Geometric Algebra* (1957), Chapter III, for symplectic bases and Witt's theorem.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module Submodule

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherian R M]
  {B : BilinForm R M}

/-- Every isotropic submodule of an alternating form lies in a self-orthogonal submodule. A
maximal isotropic submodule containing it is self-orthogonal. No nondegeneracy is needed. -/
theorem IsAlt.exists_le_eq_orthogonal (hB : B.IsAlt) {U : Submodule R M}
    (hU : U ≤ B.orthogonal U) : ∃ L, U ≤ L ∧ L = B.orthogonal L := by
  obtain ⟨L, ⟨hUL, hL⟩, hmax⟩ := WellFoundedGT.exists_maximal
    (inferInstance : WellFoundedGT (Submodule R M)) {W | U ≤ W ∧ W ≤ B.orthogonal W} ⟨U, le_rfl, hU⟩
  refine ⟨L, hUL, le_antisymm hL fun v hv ↦ ?_⟩
  have hle : L ⊔ R ∙ v ≤ L :=
    hmax ⟨hUL.trans le_sup_left, hB.sup_span_singleton_le_orthogonal hL hv⟩ le_sup_left
  exact hle (mem_sup_right (mem_span_singleton_self v))

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : BilinForm K V}

/-- An isotropic subspace for a nondegenerate form is self-orthogonal exactly when it has half
the dimension of the ambient space. -/
theorem eq_orthogonal_iff_two_mul_finrank_eq (hnd : B.Nondegenerate) {U : Submodule K V}
    (hU : U ≤ B.orthogonal U) : U = B.orthogonal U ↔ 2 * finrank K U = finrank K V := by
  have horth := B.finrank_orthogonal hnd U
  have hle := Submodule.finrank_le U
  refine ⟨fun h ↦ ?_, fun h ↦ eq_of_le_of_finrank_le hU (by omega)⟩
  rw [← h] at horth
  omega

/-- For an alternating form on a finite-dimensional space, there are isotropic subspaces of every
dimension `r` with `2 * r ≤ dim V`; the form may be degenerate. For a nondegenerate form,
`LinearMap.BilinForm.two_mul_finrank_le_finrank_of_le_orthogonal` shows that there are no others. -/
theorem IsAlt.exists_finrank_eq_of_two_mul_le (hB : B.IsAlt) {r : ℕ} (hr : 2 * r ≤ finrank K V) :
    ∃ U : Submodule K V, U ≤ B.orthogonal U ∧ finrank K U = r := by
  obtain ⟨L, -, hL⟩ := hB.exists_le_eq_orthogonal (bot_le : (⊥ : Submodule K V) ≤ _)
  have hLdim := finrank_le_two_mul_finrank_of_orthogonal_le hL.ge
  -- The span of the first `r` vectors of a basis of `L` is isotropic of dimension `r`.
  let b := finBasis K L
  let v : Fin r → V := fun i ↦ b (Fin.castLE (by omega) i)
  have hv : LinearIndependent K v :=
    (b.linearIndependent.comp _ (Fin.castLE_injective _)).map' L.subtype L.ker_subtype
  have hvL : span K (Set.range v) ≤ L := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (b _).2)
  exact ⟨_, hvL.trans (hL.le.trans (orthogonal_le hvL)), by
    rw [finrank_span_eq_card hv, Fintype.card_fin]⟩

/-- **Isotropic bases extend to symplectic bases.** Let `B` be a nondegenerate alternating form on
a space of dimension `2 * (card ι + card κ)`. A basis `e` of an isotropic subspace, indexed by `ι`,
extends to a basis of the space indexed by `(ι ⊕ κ) ⊕ (ι ⊕ κ)` in which `B` has Gram matrix
`Matrix.J`; the vectors of `e` occupy the positions `Sum.inl (Sum.inl i)`. -/
theorem IsAlt.exists_basis_toMatrix_eq_J_inl_inl_eq (hB : B.IsAlt) (hnd : B.Nondegenerate)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {U : Submodule K V}
    (e : Basis ι K U) (hU : U ≤ B.orthogonal U)
    (hdim : 2 * (Fintype.card ι + Fintype.card κ) = finrank K V) :
    ∃ b : Basis ((ι ⊕ κ) ⊕ (ι ⊕ κ)) K V,
      toMatrix b B = Matrix.J (ι ⊕ κ) K ∧ ∀ i, b (Sum.inl (Sum.inl i)) = (e i : V) := by
  obtain ⟨L, hUL, hL⟩ := hB.exists_le_eq_orthogonal hU
  have hLdim := (eq_orthogonal_iff_two_mul_finrank_eq hnd hL.le).mp hL
  -- Read `U` inside `L` and choose a complement `C` of it there.
  let U' : Submodule K L := U.comap L.subtype
  let eU' : Basis ι K U' := e.map (comapSubtypeEquivOfLe hUL).symm
  obtain ⟨C, hC⟩ := U'.exists_isCompl
  have hCdim : finrank K C = Fintype.card κ := by
    have := finrank_add_eq_of_isCompl hC
    rw [finrank_eq_card_basis eU'] at this
    omega
  let c : Basis κ K C :=
    (finBasisOfFinrankEq K C hCdim).reindex (Fintype.equivFinOfCardEq rfl).symm
  -- A basis of `L` beginning with the basis of `U`, then the symplectic extension.
  let bL : Basis (ι ⊕ κ) K L := (eU'.prod c).map (prodEquivOfIsCompl U' C hC)
  obtain ⟨b, hbJ, hb⟩ := hB.exists_basis_toMatrix_eq_J_inl_eq hnd bL hL
  refine ⟨b, hbJ, fun i ↦ ?_⟩
  simp only [hb, bL, eU', Basis.map_apply, Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
    LinearMap.inl_apply, coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]
  rw [← comapSubtypeEquivOfLe_apply_coe hUL, LinearEquiv.apply_symm_apply]

/-- **Witt's theorem for alternating forms.** For a nondegenerate alternating form on a
finite-dimensional space, any two isotropic subspaces of the same dimension are related by an
isometry of the form. This holds in every characteristic, including two. -/
theorem IsAlt.exists_isometryEquiv_map_eq (hB : B.IsAlt) (hnd : B.Nondegenerate)
    {U₁ U₂ : Submodule K V} (h₁ : U₁ ≤ B.orthogonal U₁) (h₂ : U₂ ≤ B.orthogonal U₂)
    (h : finrank K U₁ = finrank K U₂) : ∃ g : B.IsometryEquiv B, U₁.map (g : V →ₗ[K] V) = U₂ := by
  obtain ⟨m, hm⟩ := hB.even_finrank hnd
  have hr := two_mul_finrank_le_finrank_of_le_orthogonal hnd h₁
  let e₁ : Basis (Fin (finrank K U₁)) K U₁ := finBasisOfFinrankEq K U₁ rfl
  let e₂ : Basis (Fin (finrank K U₁)) K U₂ := finBasisOfFinrankEq K U₂ h.symm
  have hdim : 2 * (Fintype.card (Fin (finrank K U₁)) + Fintype.card (Fin (m - finrank K U₁))) =
      finrank K V := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨b₁, hb₁, he₁⟩ := hB.exists_basis_toMatrix_eq_J_inl_inl_eq hnd e₁ h₁ hdim
  obtain ⟨b₂, hb₂, he₂⟩ := hB.exists_basis_toMatrix_eq_J_inl_inl_eq hnd e₂ h₂ hdim
  -- The automorphism matching the two symplectic bases preserves `B`.
  let g : V ≃ₗ[K] V := b₁.equiv b₂ (Equiv.refl _)
  have hg : B.comp g.toLinearMap g.toLinearMap = B := ext_basis b₁ fun i j ↦ by
    rw [comp_apply, LinearEquiv.coe_coe, Basis.equiv_apply, Basis.equiv_apply, Equiv.refl_apply,
      Equiv.refl_apply, ← toMatrix_apply, ← toMatrix_apply, hb₁, hb₂]
  refine ⟨⟨g, fun x y ↦ congr($hg x y)⟩, ?_⟩
  -- Both subspaces are spanned by the first vectors of their symplectic bases.
  have hspan (U : Submodule K V) (e : Basis (Fin (finrank K U₁)) K U) :
      span K (Set.range fun i ↦ (e i : V)) = U := by
    have h := congrArg (map U.subtype) e.span_eq
    rwa [map_span, map_subtype_top, ← Set.range_comp] at h
  rw [← hspan U₁ e₁, ← hspan U₂ e₂, map_span, ← Set.range_comp]
  refine congrArg (fun v ↦ span K (Set.range v)) (funext fun i ↦ ?_)
  simp [g, ← he₁, ← he₂]

end Field

end LinearMap.BilinForm
