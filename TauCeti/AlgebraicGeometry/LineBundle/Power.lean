/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Tensor powers of line bundles

For a line bundle `L` on a scheme `X` and `n : ℕ`, the tensor power `L^{⊗n}` is the line bundle
defined recursively by `L^{⊗0} = 𝒪_X` and `L^{⊗(n+1)} = L^{⊗n} ⊗ L`.
These powers retain invertibility as bundled line bundles and provide the objects used in
global generation and ample twisting. They use `InvertibleSheaf.tensorProduct`, the operation
defining multiplication in `LineBundleClass`, rather than the monoidal product of `X.Modules`.
An isomorphism `e : L ≅ K` induces a specified isomorphism `L^{⊗n} ≅ K^{⊗n}`, functorial in `e`,
and the powers of the trivial line bundle are trivial by a specified isomorphism. These are the
operations on tensor powers needed to compare `n`-th roots `M^{⊗n} ≅ L` of a line bundle. The
exponent laws and the compatibility with pullback below are still only stated as the existence of
isomorphisms.

Ported from `roed-math/TauCeti-w2-fresh`, branch
`lookahead/StableReduction/relative-ampleness`, commit `efa6fc8f3735`.

## Main declarations

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorPow L n`: the tensor power `L^{⊗n}`.
* `AlgebraicGeometry.Scheme.Modules.isInvertible_tensorPow`: the monoidal tensor power
  `TauCeti.tensorPow M n` of an invertible sheaf `M` is invertible.
* `TauCeti.AlgebraicGeometry.LineBundleClass.mk_tensorPow` and
  `TauCeti.AlgebraicGeometry.LineBundleClass.mk_tensorPow_obj`: the classes of `L^{⊗n}` and of
  `TauCeti.tensorPow L.obj n` are both the `n`-th power of the class of `L` in the Picard group.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorPowCongr e n`: the isomorphism
  `L^{⊗n} ≅ K^{⊗n}` induced by `e : L ≅ K`, compatible with identities, composition and inverses
  (`tensorPowCongr_refl`, `tensorPowCongr_trans`, `tensorPowCongr_symm`); its consequence
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.nonempty_tensorPow_obj_iso` says that tensor powers
  of isomorphic line bundles are isomorphic.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorPowTrivialIso X n`: the isomorphism
  `𝒪_X^{⊗n} ≅ 𝒪_X`.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.nonempty_tensorPow_add_iso` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.nonempty_tensorPow_tensorPow_iso`: the exponent laws
  `L^{⊗(m + n)} ≅ L^{⊗m} ⊗ L^{⊗n}` and `(L^{⊗m})^{⊗n} ≅ L^{⊗(m * n)}`.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.nonempty_pullback_tensorPow_iso`: pullback commutes
  with tensor powers up to isomorphism.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.6 (the Picard group).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

namespace InvertibleSheaf

/-- The tensor power `L^{⊗n}` of a line bundle, defined by `L^{⊗0} = 𝒪_X` and
`L^{⊗(n+1)} = L^{⊗n} ⊗ L`. -/
noncomputable def tensorPow (L : InvertibleSheaf X) : ℕ → InvertibleSheaf X
  | 0 => trivial X
  | n + 1 => tensorProduct (L.tensorPow n) L

/-- The zeroth tensor power of a line bundle is the trivial line bundle. -/
@[simp]
lemma tensorPow_zero (L : InvertibleSheaf X) : L.tensorPow 0 = trivial X :=
  (rfl)

/-- The `(n + 1)`-st tensor power of `L` is `L^{⊗n} ⊗ L`. -/
lemma tensorPow_succ (L : InvertibleSheaf X) (n : ℕ) :
    L.tensorPow (n + 1) = tensorProduct (L.tensorPow n) L :=
  (rfl)

/-- An isomorphism `e : L ≅ K` of line bundles induces the isomorphism `L^{⊗n} ≅ K^{⊗n}`, applying
`e` to every factor. -/
noncomputable def tensorPowCongr {L K : InvertibleSheaf X} (e : L ≅ K) :
    (n : ℕ) → L.tensorPow n ≅ K.tensorPow n
  | 0 => Iso.refl _
  | n + 1 => tensorProductCongrLeft (tensorPowCongr e n) ≪≫ tensorProductCongrRight e

/-- On the zeroth tensor power, `tensorPowCongr e` is the identity of the trivial line bundle,
transported along `tensorPow_zero`. -/
@[simp]
lemma tensorPowCongr_zero {L K : InvertibleSheaf X} (e : L ≅ K) :
    tensorPowCongr e 0 = eqToIso (L.tensorPow_zero.trans K.tensorPow_zero.symm) := by
  ext1
  exact (eqToHom_refl _ rfl).symm

/-- The recursive step of `tensorPowCongr`: on `L^{⊗(n+1)} = L^{⊗n} ⊗ L` it applies
`tensorPowCongr e n` to the first factor and `e` to the second. -/
lemma tensorPowCongr_succ {L K : InvertibleSheaf X} (e : L ≅ K) (n : ℕ) :
    tensorPowCongr e (n + 1) =
      eqToIso (L.tensorPow_succ n) ≪≫
        (tensorProductCongrLeft (tensorPowCongr e n) ≪≫ tensorProductCongrRight e) ≪≫
          eqToIso (K.tensorPow_succ n).symm := by
  ext1
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The tensor power of the identity is the identity. -/
@[simp]
lemma tensorPowCongr_refl (L : InvertibleSheaf X) (n : ℕ) :
    tensorPowCongr (Iso.refl L) n = Iso.refl _ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [tensorPowCongr_succ, ih, tensorProductCongrLeft_refl, tensorProductCongrRight_refl]

/-- Tensor powers of isomorphisms respect composition. -/
@[simp]
lemma tensorPowCongr_trans {L K M : InvertibleSheaf X} (e : L ≅ K) (e' : K ≅ M) (n : ℕ) :
    tensorPowCongr (e ≪≫ e') n = tensorPowCongr e n ≪≫ tensorPowCongr e' n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [tensorPowCongr_succ, ih, tensorProductCongrLeft_trans,
      tensorProductCongrRight_trans, Iso.trans_assoc]
    rw [← Iso.trans_assoc (eqToIso _) (eqToIso _), eqToIso_trans, eqToIso_refl, Iso.refl_trans,
      ← Iso.trans_assoc (tensorProductCongrLeft (tensorPowCongr e' n)),
      tensorProductCongrLeft_trans_tensorProductCongrRight, Iso.trans_assoc]

/-- The tensor power of the inverse of an isomorphism is the inverse of its tensor power. -/
@[simp]
lemma tensorPowCongr_symm {L K : InvertibleSheaf X} (e : L ≅ K) (n : ℕ) :
    tensorPowCongr e.symm n = (tensorPowCongr e n).symm := by
  ext1
  refine (Iso.inv_ext ?_).symm
  rw [← Iso.trans_hom, ← tensorPowCongr_trans, Iso.self_symm_id, tensorPowCongr_refl,
    Iso.refl_hom]

variable (X) in
/-- The `n`-th tensor power of the trivial line bundle is the trivial line bundle, removing the
trivial factors one at a time with the right unit isomorphism. -/
noncomputable def tensorPowTrivialIso : (n : ℕ) → (trivial X).tensorPow n ≅ trivial X
  | 0 => Iso.refl _
  | n + 1 => tensorTrivialRightIso _ ≪≫ tensorPowTrivialIso n

/-- On the zeroth tensor power, `tensorPowTrivialIso` is the transport along `tensorPow_zero`. -/
@[simp]
lemma tensorPowTrivialIso_zero : tensorPowTrivialIso X 0 = eqToIso (trivial X).tensorPow_zero := by
  ext1
  exact (eqToHom_refl _ rfl).symm

/-- The recursive step of `tensorPowTrivialIso`: on `𝒪_X^{⊗(n+1)} = 𝒪_X^{⊗n} ⊗ 𝒪_X` it removes
the last factor and then applies `tensorPowTrivialIso X n`. -/
lemma tensorPowTrivialIso_succ (n : ℕ) :
    tensorPowTrivialIso X (n + 1) =
      eqToIso ((trivial X).tensorPow_succ n) ≪≫
        tensorTrivialRightIso ((trivial X).tensorPow n) ≪≫ tensorPowTrivialIso X n := by
  ext1
  exact (Category.id_comp _).symm

end InvertibleSheaf

namespace InvertibleSheaf

/-- Every monoidal tensor power `TauCeti.tensorPow M n` of an invertible sheaf `M` is invertible. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isInvertible_tensorPow (M : X.Modules)
    [SheafOfModules.isInvertible X M] (n : ℕ) :
    SheafOfModules.isInvertible X (TauCeti.tensorPow M n) := by
  induction n with
  | zero => exact SheafOfModules.isInvertible_tensorUnit X
  | succ n ih => exact AlgebraicGeometry.Scheme.Modules.isInvertible_tensorObj M _

end InvertibleSheaf

namespace LineBundleClass

/-- The class of the tensor power `L^{⊗n}` is the `n`-th power of the class of `L`. -/
@[simp]
lemma mk_tensorPow (L : InvertibleSheaf X) (n : ℕ) : mk (L.tensorPow n) = mk L ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [InvertibleSheaf.tensorPow_succ, ih, pow_succ]

/-- The class of the monoidal tensor power `TauCeti.tensorPow L.obj n` is the `n`-th power of the
class of `L`. -/
@[simp]
lemma mk_tensorPow_obj (L : InvertibleSheaf X) (n : ℕ) :
    mk ⟨TauCeti.tensorPow L.obj n, inferInstance⟩ = mk L ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact mk_eq_one_iff.mpr ⟨Iso.refl _⟩
  | succ n ih =>
    rw [pow_succ', ← ih, ← mk_tensorProduct]
    exact mk_eq_mk_iff.mpr
      ⟨(InvertibleSheaf.tensorProductObjIso L ⟨TauCeti.tensorPow L.obj n, inferInstance⟩).symm⟩

end LineBundleClass

namespace InvertibleSheaf

/-- The underlying sheaves of `L^{⊗n}` and `K^{⊗n}` are isomorphic whenever the underlying sheaves
of `L` and `K` are. -/
theorem nonempty_tensorPow_obj_iso {L K : InvertibleSheaf X} (h : Nonempty (L.obj ≅ K.obj))
    (n : ℕ) : Nonempty ((L.tensorPow n).obj ≅ (K.tensorPow n).obj) :=
  h.map fun e ↦ (SheafOfModules.isInvertible X).ι.mapIso
    (tensorPowCongr (ObjectProperty.isoMk _ e) n)

/-- The tensor power `L^{⊗(m + n)}` is isomorphic to `L^{⊗m} ⊗ L^{⊗n}`. -/
theorem nonempty_tensorPow_add_iso (L : InvertibleSheaf X) (m n : ℕ) :
    Nonempty ((L.tensorPow (m + n)).obj ≅ (tensorProduct (L.tensorPow m) (L.tensorPow n)).obj) := by
  rw [← LineBundleClass.mk_eq_mk_iff]
  simp [pow_add]

/-- The tensor power `(L^{⊗m})^{⊗n}` is isomorphic to `L^{⊗(m * n)}`. -/
theorem nonempty_tensorPow_tensorPow_iso (L : InvertibleSheaf X) (m n : ℕ) :
    Nonempty (((L.tensorPow m).tensorPow n).obj ≅ (L.tensorPow (m * n)).obj) := by
  rw [← LineBundleClass.mk_eq_mk_iff]
  simp [pow_mul]

/-- **Pullback commutes with tensor powers.** For `f : X ⟶ Y` and a line bundle `L` on `Y`, the
pullback of `L^{⊗n}` is isomorphic to `(f^* L)^{⊗n}`. -/
theorem nonempty_pullback_tensorPow_iso (f : X ⟶ Y) (L : InvertibleSheaf Y) (n : ℕ) :
    Nonempty (((pullback f).obj (L.tensorPow n)).obj ≅ (((pullback f).obj L).tensorPow n).obj) := by
  rw [← LineBundleClass.mk_eq_mk_iff, ← LineBundleClass.pullback_mk]
  simp

end InvertibleSheaf

end AlgebraicGeometry

end TauCeti
