/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Algebra.Module.Submodule.Quotient
public import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# Extending a submodule basis by a quotient basis, indexed by `Fin (m + n)`

`Module.Basis.sumQuot` combines a basis of a submodule `p` of `V` with a basis of `V ⧸ p` into a
basis of `V` indexed by a sum type. An induction on `Module.finrank` wants that basis indexed by
`Fin (m + n)` instead, so that the two blocks are picked out by `Fin.castAdd` and `Fin.natAdd` and
the resulting matrices are visibly block triangular.

This file records that reindexing together with the six equations locating the blocks: what the
basis is on each block, what the coordinates of a vector are there, and the two `_of_mem` variants
stated for an ambient vector known to lie in the submodule. It then computes the matrix, in this
basis, of an endomorphism preserving the submodule: its diagonal blocks are the matrices of the
restriction and of the induced endomorphism of the quotient, and its lower-left block vanishes. So
the matrix is upper (uni)triangular as soon as both diagonal blocks are.

## Main definitions

* `TauCeti.extensionBasis`: the `Fin (m + n)`-indexed basis of `V` built from a basis of `p` and a
  basis of `V ⧸ p`.

## Main results

* `TauCeti.extensionBasis_castAdd` and `TauCeti.extensionBasis_natAdd_mkQ`: the basis vectors on
  the two blocks.
* `TauCeti.extensionBasis_repr_castAdd` and `TauCeti.extensionBasis_repr_natAdd`: the coordinates
  of a vector on the two blocks.
* `TauCeti.extensionBasis_repr_castAdd_of_mem` and `TauCeti.extensionBasis_repr_natAdd_of_mem`: the
  same for an ambient vector known to lie in the submodule, whose second-block coordinates vanish.
* `TauCeti.toMatrixAlgEquiv_extensionBasis_castAdd_castAdd`,
  `TauCeti.toMatrixAlgEquiv_extensionBasis_natAdd_castAdd` and
  `TauCeti.toMatrixAlgEquiv_extensionBasis_natAdd_natAdd`: the blocks of the matrix of an
  endomorphism preserving the submodule.
* `TauCeti.toMatrixAlgEquiv_extensionBasis_isUpperTriangular` and
  `TauCeti.toMatrixAlgEquiv_extensionBasis_isUpperUnitriangular`: that matrix is upper
  (uni)triangular when both of its diagonal blocks are.
-/

public section

namespace TauCeti

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {m n : ℕ}

open Module

/-- Extend bases of a submodule and of its quotient to a basis of the ambient module, indexed by
`Fin (m + n)`. -/
noncomputable def extensionBasis (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) : Basis (Fin (m + n)) R V :=
  (bp.sumQuot bq).reindex finSumFinEquiv

/-- On the first block, `extensionBasis` is the given basis of the submodule. -/
@[simp]
theorem extensionBasis_castAdd (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) (i : Fin m) :
    extensionBasis p bp bq (Fin.castAdd n i) = bp i := by
  rw [extensionBasis, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
    Basis.sumQuot_inl]

/-- On the second block, `extensionBasis` lifts the given basis of the quotient. -/
@[simp]
theorem extensionBasis_natAdd_mkQ (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) (j : Fin n) :
    Submodule.Quotient.mk (extensionBasis p bp bq (Fin.natAdd m j)) = bq j := by
  rw [extensionBasis, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd,
    Basis.sumQuot_inr]

/-- The first-block coordinates of a vector of the submodule are its coordinates there.

Not a `simp` lemma: `extensionBasis_repr_castAdd_of_mem` is the `simp` normal form, matching how
Mathlib annotates `Module.Basis.sumQuot_repr_inl` and `sumQuot_repr_inl_of_mem`. -/
theorem extensionBasis_repr_castAdd (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) (x : p) (i : Fin m) :
    (extensionBasis p bp bq).repr x (Fin.castAdd n i) = bp.repr x i := by
  rw [extensionBasis, Basis.repr_reindex_apply, finSumFinEquiv_symm_apply_castAdd,
    Basis.sumQuot_repr_inl]

/-- The second-block coordinates of a vector are the coordinates of its quotient class. -/
@[simp]
theorem extensionBasis_repr_natAdd (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) (x : V) (j : Fin n) :
    (extensionBasis p bp bq).repr x (Fin.natAdd m j) = bq.repr (p.mkQ x) j := by
  rw [extensionBasis, Basis.repr_reindex_apply, finSumFinEquiv_symm_apply_natAdd,
    Basis.sumQuot_repr_inr]

/-- The first-block coordinates of an ambient vector lying in the submodule are its coordinates
there. -/
@[simp]
theorem extensionBasis_repr_castAdd_of_mem (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) (x : V) (hx : x ∈ p) (i : Fin m) :
    (extensionBasis p bp bq).repr x (Fin.castAdd n i) = bp.repr ⟨x, hx⟩ i :=
  extensionBasis_repr_castAdd p bp bq ⟨x, hx⟩ i

/-- A vector of the submodule has no second-block coordinates: this is the vanishing of the
off-diagonal block.

Not a `simp` lemma: `extensionBasis_repr_natAdd` above already is, so this left-hand side is not in
`simp` normal form and marking it trips `simpNF`. Mathlib annotates its `sumQuot` counterparts the
same way — `sumQuot_repr_inr` is `simp` and `sumQuot_repr_inr_of_mem` is not. -/
theorem extensionBasis_repr_natAdd_of_mem (p : Submodule R V) (bp : Basis (Fin m) R p)
    (bq : Basis (Fin n) R (V ⧸ p)) (x : V) (hx : x ∈ p) (j : Fin n) :
    (extensionBasis p bp bq).repr x (Fin.natAdd m j) = 0 := by
  rw [extensionBasis_repr_natAdd, Submodule.mkQ_apply,
    (Submodule.Quotient.mk_eq_zero p).mpr hx, map_zero, Finsupp.coe_zero, Pi.zero_apply]

section Matrix

variable (p : Submodule R V) (bp : Basis (Fin m) R p) (bq : Basis (Fin n) R (V ⧸ p))
variable {f : Module.End R V} (hf : p ≤ p.comap f)

-- The three block lemmas are conditional `simp` lemmas: `simp` discharges the invariance
-- hypothesis `hf` only when it is supplied, as in `simp [hf]`.

/-- In the basis `extensionBasis p bp bq`, the diagonal block of an endomorphism `f` preserving `p`
indexed by the basis `bp` of `p` is the matrix of the restriction of `f` to `p`. -/
@[simp]
theorem toMatrixAlgEquiv_extensionBasis_castAdd_castAdd (i j : Fin m) :
    LinearMap.toMatrixAlgEquiv (extensionBasis p bp bq) f (Fin.castAdd n i) (Fin.castAdd n j) =
      LinearMap.toMatrixAlgEquiv bp (f.restrict fun _ hx ↦ Submodule.mem_comap.mp (hf hx)) i j := by
  rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrixAlgEquiv_apply, extensionBasis_castAdd,
    extensionBasis_repr_castAdd_of_mem p bp bq _ (Submodule.mem_comap.mp (hf (bp j).2)),
    LinearMap.restrict_apply]

include hf in
/-- In the basis `extensionBasis p bp bq`, the lower-left block of the matrix of an endomorphism
preserving `p` vanishes. -/
@[simp]
theorem toMatrixAlgEquiv_extensionBasis_natAdd_castAdd (i : Fin n) (j : Fin m) :
    LinearMap.toMatrixAlgEquiv (extensionBasis p bp bq) f (Fin.natAdd m i) (Fin.castAdd n j) =
      0 := by
  rw [LinearMap.toMatrixAlgEquiv_apply, extensionBasis_castAdd]
  exact extensionBasis_repr_natAdd_of_mem p bp bq _ (Submodule.mem_comap.mp (hf (bp j).2)) i

/-- In the basis `extensionBasis p bp bq`, the diagonal block of an endomorphism `f` preserving `p`
indexed by the basis `bq` of `V ⧸ p` is the matrix of the endomorphism of `V ⧸ p` induced by
`f`. -/
@[simp]
theorem toMatrixAlgEquiv_extensionBasis_natAdd_natAdd (i j : Fin n) :
    LinearMap.toMatrixAlgEquiv (extensionBasis p bp bq) f (Fin.natAdd m i) (Fin.natAdd m j) =
      LinearMap.toMatrixAlgEquiv bq (p.mapQ p f hf) i j := by
  rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrixAlgEquiv_apply,
    extensionBasis_repr_natAdd, ← extensionBasis_natAdd_mkQ p bp bq j, Submodule.mkQ_apply,
    Submodule.mapQ_apply]

/-- If an endomorphism `f` preserves a submodule `p` and its restriction to `p` and the induced
endomorphism of `V ⧸ p` have upper-triangular matrices in the bases `bp` and `bq`, then the
matrix of `f` in the extension basis `extensionBasis p bp bq` is upper triangular. -/
theorem toMatrixAlgEquiv_extensionBasis_isUpperTriangular
    (hp : (LinearMap.toMatrixAlgEquiv bp
      (f.restrict fun _ hx ↦ Submodule.mem_comap.mp (hf hx))).IsUpperTriangular)
    (hq : (LinearMap.toMatrixAlgEquiv bq (p.mapQ p f hf)).IsUpperTriangular) :
    (LinearMap.toMatrixAlgEquiv (extensionBasis p bp bq) f).IsUpperTriangular := by
  intro i j hji
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;>
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, id_eq, hf,
      toMatrixAlgEquiv_extensionBasis_castAdd_castAdd,
      toMatrixAlgEquiv_extensionBasis_natAdd_castAdd,
      toMatrixAlgEquiv_extensionBasis_natAdd_natAdd] at hji ⊢
  · exact hp ((Fin.strictMono_castAdd n).lt_iff_lt.mp hji)
  · -- A quotient index lies after every submodule index.
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at hji
    omega
  · exact hq ((Fin.strictMono_natAdd m).lt_iff_lt.mp hji)

/-- If an endomorphism `f` preserves a submodule `p` and its restriction to `p` and the induced
endomorphism of `V ⧸ p` have upper-unitriangular matrices in the bases `bp` and `bq`, then the
matrix of `f` in the extension basis `extensionBasis p bp bq` is upper unitriangular. -/
theorem toMatrixAlgEquiv_extensionBasis_isUpperUnitriangular
    (hp : (LinearMap.toMatrixAlgEquiv bp
      (f.restrict fun _ hx ↦ Submodule.mem_comap.mp (hf hx))).IsUpperUnitriangular)
    (hq : (LinearMap.toMatrixAlgEquiv bq (p.mapQ p f hf)).IsUpperUnitriangular) :
    (LinearMap.toMatrixAlgEquiv (extensionBasis p bp bq) f).IsUpperUnitriangular := by
  rw [Matrix.isUpperUnitriangular_def]
  refine ⟨toMatrixAlgEquiv_extensionBasis_isUpperTriangular p bp bq hf hp.isUpperTriangular
    hq.isUpperTriangular, fun i ↦ ?_⟩
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i
  · rw [finSumFinEquiv_apply_left, toMatrixAlgEquiv_extensionBasis_castAdd_castAdd p bp bq hf]
    exact hp.apply_diag i
  · rw [finSumFinEquiv_apply_right, toMatrixAlgEquiv_extensionBasis_natAdd_natAdd p bp bq hf]
    exact hq.apply_diag i

end Matrix

end TauCeti

namespace LinearMap

open Module

variable {k V W : Type*} [CommRing k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {m n : ℕ}
variable (f : V →ₗ[k] W) (I : Submodule k V) (hker : LinearMap.ker f ≤ I)
variable (bImage : Basis (Fin m) k (I.map f.rangeRestrict))
  (bQuot : Basis (Fin n) k (V ⧸ I))

/-- Extend bases of the image of a submodule and of its quotient to a basis of a map's range. -/
noncomputable def rangeExtensionBasis : Basis (Fin (m + n)) k f.range :=
  TauCeti.extensionBasis (I.map f.rangeRestrict) bImage
    (bQuot.map (LinearMap.quotientEquivRangeQuotientMap f I hker))

/-- The quotient block of the range extension basis is the transported quotient basis. -/
theorem rangeExtensionBasis_natAdd_mkQ (j : Fin n) :
    Submodule.Quotient.mk (rangeExtensionBasis f I hker bImage bQuot (Fin.natAdd m j)) =
      LinearMap.quotientEquivRangeQuotientMap f I hker (bQuot j) := by
  rw [rangeExtensionBasis, TauCeti.extensionBasis_natAdd_mkQ, Module.Basis.map_apply]

/-- The image block of the range extension basis is the given image basis. -/
theorem rangeExtensionBasis_castAdd (i : Fin m) :
    rangeExtensionBasis f I hker bImage bQuot (Fin.castAdd n i) = bImage i := by
  rw [rangeExtensionBasis, TauCeti.extensionBasis_castAdd]

end LinearMap
