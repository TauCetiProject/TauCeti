/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
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

## Main declarations

* `TauCeti.groupLikeBaseChange`: the canonical scalar-extension map on characters.
* `TauCeti.groupLikeBaseChange_injective`: injectivity along a faithfully flat extension.
* `TauCeti.span_groupLike_eq_top_of_surjective`: spanning by group-like elements descends
  when every extended character descends.
* `TauCeti.groupLikeBaseChange_bijective`: preservation of characters under the stated
  spanning, torsion-free, and connected-spectrum hypotheses.
* `TauCeti.groupLikeBaseChangeEquiv`: the resulting multiplicative equivalence.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 12.7 and Theorems 12.8--12.9.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R K A : Type*} [CommSemiring R] [CommSemiring K] [Algebra R K]
  [Semiring A] [Bialgebra R A]

/-- Scalar extension of a group-like element, sending `g` to `1 ⊗ g`. -/
noncomputable def groupLikeBaseChange :
    _root_.GroupLike R A →* _root_.GroupLike K (K ⊗[R] A) where
  toFun g := ⟨1 ⊗ₜ[R] g.val, {
    counit_eq_one := by simp
    comul_eq_tmul_self := by
      simp [TensorProduct.comul_tmul, g.isGroupLikeElem_val.comul_eq_tmul_self] }⟩
  map_one' := _root_.GroupLike.val_injective (by simp [Algebra.TensorProduct.one_def])
  map_mul' g h := _root_.GroupLike.val_injective (by simp [Algebra.TensorProduct.tmul_mul_tmul])

/-- The underlying value of an extended character. -/
@[simp]
theorem val_groupLikeBaseChange (g : _root_.GroupLike R A) :
    (groupLikeBaseChange (K := K) g).val = 1 ⊗ₜ[R] g.val := (rfl)

/-- Extending a character commutes with a bialgebra morphism. -/
@[simp]
theorem groupLikeBaseChange_mapGroupLike {B : Type*} [Semiring B] [Bialgebra R B]
    (f : A →ₐc[R] B) (g : _root_.GroupLike R A) :
    groupLikeBaseChange (K := K) (f.mapGroupLike g) =
      (Bialgebra.TensorProduct.map (BialgHom.id K K) f).mapGroupLike (groupLikeBaseChange g) := by
  apply _root_.GroupLike.val_injective
  simp

/-- Scalar extension of characters is injective along a faithfully flat extension of the
base ring. No spanning hypothesis is needed. -/
theorem groupLikeBaseChange_injective {R K A : Type*} [CommRing R] [CommRing K] [Algebra R K]
    [Module.FaithfullyFlat R K] [Ring A] [Bialgebra R A] :
    Function.Injective (groupLikeBaseChange (R := R) (K := K) (A := A)) := fun _ _ h ↦
  _root_.GroupLike.val_injective <|
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := K) A
      (congrArg _root_.GroupLike.val h)

/-- Spanning by group-like elements descends along a faithfully flat extension of the base ring
when every character over the extension comes from one over the base. -/
theorem span_groupLike_eq_top_of_surjective {R K A : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [Module.FaithfullyFlat R K] [Ring A] [Bialgebra R A]
    (hsurj : Function.Surjective (groupLikeBaseChange (R := R) (K := K) (A := A)))
    (hspan : Submodule.span K
      (Set.range (_root_.GroupLike.val (R := K) (A := K ⊗[R] A))) = ⊤) :
    Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := A))) = ⊤ := by
  let p := Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := A)))
  have hp : p.baseChange K = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    obtain ⟨h, rfl⟩ := hsurj g
    rw [val_groupLikeBaseChange]
    exact p.tmul_mem_baseChange_of_mem 1 (Submodule.subset_span ⟨h, rfl⟩)
  apply Submodule.baseChange_injective (A := K)
  simpa only [Submodule.baseChange_top] using hp

section Split

variable {R K A : Type*} [CommRing R] [IsDomain R] [CommRing K] [Algebra R K]
  [ConnectedSpace (PrimeSpectrum K)] [CommRing A] [Bialgebra R A]
  [Module.IsTorsionFree R A]

/-- Scalar extension preserves the characters of a torsion-free commutative bialgebra
spanned by group-like elements, provided the extended base has connected prime spectrum.
The `ConnectedSpace` hypothesis includes nonemptiness, so the extended base is nontrivial. -/
theorem groupLikeBaseChange_bijective
    (hspan : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := A))) = ⊤) :
    Function.Bijective (groupLikeBaseChange (R := R) (K := K) (A := A)) := by
  let e := GroupLike.evaluationBialgEquiv R A hspan
  let f := Bialgebra.TensorProduct.map (BialgHom.id K K) e.toBialgHom
  have hf : Function.Bijective f := by
    have hmap : Algebra.TensorProduct.map (AlgHom.id R K) e.toAlgEquiv.toAlgHom =
        f.toAlgHom.restrictScalars R := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [f]
    rw [← BialgHom.coe_toAlgHom f, ← AlgHom.coe_restrictScalars' R, ← hmap]
    exact Algebra.TensorProduct.map_bijective Function.bijective_id e.bijective
  let eK := (MonoidAlgebra.scalarTensorBialgEquiv R K
    (G := _root_.GroupLike R A)).symm.trans
    (BialgEquiv.ofBijective f hf)
  let q := (TauCeti.MonoidAlgebra.groupLikeEquiv (R := K)
    (H := _root_.GroupLike R A)).symm.trans eK.mapGroupLike
  have hq (g : _root_.GroupLike R A) : q g = groupLikeBaseChange (K := K) g := by
    apply _root_.GroupLike.val_injective
    simp only [q, eK, f, e, BialgEquiv.toBialgHom_eq_coe,
      GroupLike.evaluationBialgEquiv_toBialgHom, BialgEquiv.mapGroupLike_trans,
      MulEquiv.trans_apply, BialgEquiv.val_mapGroupLike,
      TauCeti.MonoidAlgebra.val_groupLikeEquiv_symm,
      MonoidAlgebra.scalarTensorBialgEquiv_symm_single,
      BialgEquiv.ofBijective_apply, Bialgebra.TensorProduct.map_tmul,
      BialgHom.id_apply, MonoidAlgebra.liftGroupLikeBialgHom_single, one_smul,
      val_groupLikeBaseChange]
  have hfun : (q : _ → _) = groupLikeBaseChange (R := R) (K := K) (A := A) := funext hq
  rw [← hfun]
  exact q.bijective

/-- The character equivalence induced by scalar extension of a split commutative bialgebra.
Its forward map is the canonical scalar-extension map, independently of the spanning proof. -/
noncomputable def groupLikeBaseChangeEquiv
    (hspan : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := A))) = ⊤) :
    _root_.GroupLike R A ≃* _root_.GroupLike K (K ⊗[R] A) :=
  MulEquiv.ofBijective groupLikeBaseChange (groupLikeBaseChange_bijective hspan)

/-- The equivalence applies as the canonical scalar-extension map. -/
@[simp]
theorem groupLikeBaseChangeEquiv_apply
    (hspan : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := A))) = ⊤)
    (g : _root_.GroupLike R A) :
    groupLikeBaseChangeEquiv (K := K) hspan g = groupLikeBaseChange g := (rfl)

/-- Every extended character is the tensor with one of its unique original character. -/
@[simp]
theorem one_tmul_val_groupLikeBaseChangeEquiv_symm
    (hspan : Submodule.span R (Set.range (_root_.GroupLike.val (R := R) (A := A))) = ⊤)
    (g : _root_.GroupLike K (K ⊗[R] A)) :
    1 ⊗ₜ[R] ((groupLikeBaseChangeEquiv (K := K) hspan).symm g).val = g.val := by
  rw [← val_groupLikeBaseChange, ← groupLikeBaseChangeEquiv_apply hspan,
    MulEquiv.apply_symm_apply]

end Split

end TauCeti
