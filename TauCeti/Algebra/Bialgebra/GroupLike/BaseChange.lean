/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.BaseChange
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.GroupLike

/-!
# Scalar extension of characters of a split bialgebra

Scalar extension sends a group-like element `g` to `1 ⊗ g`. If a commutative bialgebra over
a domain is torsion-free and spanned by its group-like elements, this map is an equivalence
for every scalar extension with connected prime spectrum. In particular, extending the
splitting field of a diagonalizable group does not create new characters. This allows
characters computed over a splitting field to be compared with geometric characters.

Here `ConnectedSpace (PrimeSpectrum K)` includes nonemptiness of the spectrum and hence
implies `Nontrivial K`; in particular, the zero ring is excluded.

The proof uses `GroupLike.evaluationBialgEquiv` to reconstruct the original bialgebra as
the monoid algebra of its group-like elements, `MonoidAlgebra.scalarTensorBialgEquiv`
for scalar extension, and `MonoidAlgebra.groupLikeEquiv` to classify the resulting
characters. No finite-generation, smoothness, or characteristic hypothesis is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 12.7 and Theorems 12.8--12.9.
-/

public section

open scoped TensorProduct

namespace TauCeti.GroupLike

variable {R K A : Type*} [CommSemiring R] [CommSemiring K] [Algebra R K]
  [Semiring A] [Bialgebra R A]

/-- Scalar extension of a group-like element, sending `g` to `1 ⊗ g`. -/
noncomputable def baseChange :
    _root_.GroupLike R A →* _root_.GroupLike K (K ⊗[R] A) where
  toFun g := ⟨1 ⊗ₜ[R] g.val, {
    counit_eq_one := by simp
    comul_eq_tmul_self := by
      simp [TensorProduct.comul_tmul, g.isGroupLikeElem_val.comul_eq_tmul_self] }⟩
  map_one' := _root_.GroupLike.val_injective (by simp [Algebra.TensorProduct.one_def])
  map_mul' g h := _root_.GroupLike.val_injective (by simp [Algebra.TensorProduct.tmul_mul_tmul])

/-- The underlying value of an extended character. -/
@[simp]
theorem val_baseChange (g : _root_.GroupLike R A) :
    (baseChange (K := K) g).val = 1 ⊗ₜ[R] g.val := (rfl)

/-- Extending a character commutes with a bialgebra morphism. -/
@[simp]
theorem baseChange_map {B : Type*} [Semiring B] [Bialgebra R B]
    (f : A →ₐc[R] B) (g : _root_.GroupLike R A) :
    baseChange (K := K) (map f g) =
      map (Bialgebra.TensorProduct.map (BialgHom.id K K) f) (baseChange g) := by
  apply _root_.GroupLike.val_injective
  simp

section Split

variable {R K A : Type*} [CommRing R] [IsDomain R] [CommRing K] [Algebra R K]
  [ConnectedSpace (PrimeSpectrum K)] [CommRing A] [Bialgebra R A]
  [Module.IsTorsionFree R A]

/-- Scalar extension preserves the characters of a torsion-free commutative bialgebra
spanned by group-like elements, provided the extended base has connected prime spectrum.
The `ConnectedSpace` hypothesis includes nonemptiness, so the extended base is nontrivial. -/
theorem baseChange_bijective
    (hspan : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := A))) = ⊤) :
    Function.Bijective (baseChange (R := R) (K := K) (A := A)) := by
  let e := evaluationBialgEquiv R A hspan
  let f := Bialgebra.TensorProduct.map (BialgHom.id K K) e.toBialgHom
  have hf : Function.Bijective f := by
    have hmap : Algebra.TensorProduct.map (AlgHom.id R K) e.toAlgEquiv.toAlgHom =
        f.toAlgHom.restrictScalars R := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [f]
    rw [← BialgHom.coe_toAlgHom f, ← AlgHom.coe_restrictScalars' R, ← hmap]
    exact Algebra.TensorProduct.map_bijective Function.bijective_id e.bijective
  let eK := (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv R K
    (G := _root_.GroupLike R A)).symm.trans
    (BialgEquiv.ofBijective f hf)
  let q := (TauCeti.MonoidAlgebra.groupLikeEquiv (R := K)
    (H := _root_.GroupLike R A)).symm.trans (mapEquiv eK)
  have hq (g : _root_.GroupLike R A) : q g = baseChange (K := K) g := by
    apply _root_.GroupLike.val_injective
    simp only [q, eK, f, e, BialgEquiv.toBialgHom_eq_coe,
      evaluationBialgEquiv_toBialgHom, mapEquiv_trans, MulEquiv.trans_apply,
      val_mapEquiv, TauCeti.MonoidAlgebra.val_groupLikeEquiv_symm,
      TauCeti.MonoidAlgebra.scalarTensorBialgEquiv_symm_single,
      BialgEquiv.ofBijective_apply, Bialgebra.TensorProduct.map_tmul,
      BialgHom.id_apply, evaluationBialgHom_single, one_smul, val_baseChange]
  have hfun : (q : _ → _) = baseChange (R := R) (K := K) (A := A) := funext hq
  rw [← hfun]
  exact q.bijective

/-- The character equivalence induced by scalar extension of a split commutative bialgebra.
Its forward map is the canonical scalar-extension map, independently of the spanning proof. -/
noncomputable def baseChangeEquiv
    (hspan : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := A))) = ⊤) :
    _root_.GroupLike R A ≃* _root_.GroupLike K (K ⊗[R] A) :=
  MulEquiv.ofBijective baseChange (baseChange_bijective hspan)

/-- The equivalence applies as the canonical scalar-extension map. -/
@[simp]
theorem baseChangeEquiv_apply
    (hspan : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := A))) = ⊤)
    (g : _root_.GroupLike R A) :
    baseChangeEquiv (K := K) hspan g = baseChange g := (rfl)

/-- Every extended character is the tensor with one of its unique original character. -/
@[simp]
theorem one_tmul_val_baseChangeEquiv_symm
    (hspan : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := A))) = ⊤)
    (g : _root_.GroupLike K (K ⊗[R] A)) :
    1 ⊗ₜ[R] ((baseChangeEquiv (K := K) hspan).symm g).val = g.val := by
  rw [← val_baseChange, ← baseChangeEquiv_apply hspan,
    MulEquiv.apply_symm_apply]

end Split

end TauCeti.GroupLike
