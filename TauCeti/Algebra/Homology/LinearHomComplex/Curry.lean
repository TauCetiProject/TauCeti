/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.Algebra.Homology.Monoidal.Braiding
public import TauCeti.Algebra.Homology.Monoidal.KFlat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential

/-!
# The Hom complex out of a tensor product of complexes

Let `K`, `L` and `M` be cochain complexes of modules over a commutative ring `R`. A cochain `w`
of degree `n` from the tensor product `K ⊗ L` to `M` curries to the cochain
`x ↦ (y ↦ w (x ⊗ y))` of degree `n` from `K` to the `R`-linear Hom complex `Hom(L, M)`, and this
is a bijection. With Mathlib's conventions for the differential `δ` of cochains and for the
differential `d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y` of the tensor product, currying commutes with
`δ` without any sign. It therefore gives an isomorphism of `R`-linear Hom complexes

`Hom(K ⊗ L, M) ≅ Hom(K, Hom(L, M))`,

natural in `K`, `L` and `M`. In degree zero its cocycles are the morphisms of complexes, and two
morphisms are homotopic exactly when their cocycles differ by a coboundary. So currying is a
bijection `(K ⊗ L ⟶ M) ≃ (K ⟶ Hom(L, M))`, which makes tensoring on the right with `L` left
adjoint to `Hom(L, -)`, and it preserves the homotopy relation.

This is the input from which the derived tensor-Hom adjunction on unbounded derived categories of
modules is built: if `L` is K-flat and `I` is K-injective, then `Hom(L, I)` is K-injective, because
a map from an acyclic complex `A` to `Hom(L, I)` uncurries to a map from the acyclic complex
`A ⊗ L` to `I`.

## Main definitions

* `CochainComplex.HomComplex.Cochain.curry` and `CochainComplex.HomComplex.Cochain.uncurry`, with
  the `R`-linear equivalence `CochainComplex.HomComplex.Cochain.curryLinearEquiv`.
* `TauCeti.linearHomComplexCurryIso`: the isomorphism `Hom(K ⊗ L, M) ≅ Hom(K, Hom(L, M))` of
  complexes of `R`-modules.
* `TauCeti.linearHomComplexHomEquiv`: the bijection `(K ⊗ L ⟶ M) ≃ (K ⟶ Hom(L, M))`, and
  `TauCeti.linearHomComplexHomEquivHomotopy`, the corresponding bijection of homotopies.
* `TauCeti.tensorRightLinearHomComplexAdjunction`: the adjunction `- ⊗ L ⊣ Hom(L, -)` on cochain
  complexes of `R`-modules.

## Main results

* `CochainComplex.HomComplex.Cochain.δ_curry`: currying commutes with the differentials.
* `TauCeti.linearHomComplexCurryIso_hom_naturality_fst`,
  `TauCeti.linearHomComplexCurryIso_hom_naturality_snd` and
  `TauCeti.linearHomComplexCurryIso_hom_naturality_target`: naturality in the three complexes.
* `TauCeti.isKInjective_linearHomComplex`: the Hom complex from a K-flat complex to a K-injective
  complex is K-injective.

## References

* The Stacks Project, Section 15.73, Lemma 15.73.1 (Tag 0A5Y), and the proof of
  Lemma 15.75.1 (Tag 0A65).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

universe v

namespace CochainComplex.HomComplex.Cochain

variable {R : Type v} [CommRing R] {K L M : CochainComplex (ModuleCat.{v} R) ℤ} {n : ℤ}

/-- The value `x ↦ (y ↦ w (x ⊗ y))` of the curried cochain on an element `x` of degree `p`. -/
private def curryAux (w : Cochain (K ⊗ L) M n) (p q : ℤ) (hpq : p + n = q) :
    K.X p →ₗ[R] Cochain L M q where
  toFun x := Cochain.mk fun a b hab => ModuleCat.ofHom
    ((ιTensorObj K L p a (p + a) rfl ≫ w.v (p + a) b (by omega)).hom.comp
      (TensorProduct.mk R (K.X p) (L.X a) x))
  map_add' x x' := by
    ext a b hab y
    simp
  map_smul' r x := by
    ext a b hab y
    simp only [mk_v, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.smul_apply,
      ModuleCat.hom_smul, smul_v, RingHom.id_apply]
    rw [← map_smul, TensorProduct.mk_apply, TensorProduct.mk_apply, TensorProduct.smul_tmul']

/-- The curried form `x ↦ (y ↦ w (x ⊗ y))` of a cochain `w` from `K ⊗ L` to `M`, a cochain of the
same degree from `K` to the `R`-linear Hom complex of `L` and `M`. -/
def curry (w : Cochain (K ⊗ L) M n) : Cochain K (linearHomComplex R L M) n :=
  Cochain.mk fun p q hpq => ModuleCat.ofHom (curryAux w p q hpq)

/-- The curried cochain evaluated on `x` and then on `y` is the original cochain evaluated on the
pure tensor `x ⊗ y`. -/
lemma curry_v_hom_apply_v_hom_apply (w : Cochain (K ⊗ L) M n) {p q : ℤ} (hpq : p + n = q)
    (x : K.X p) {a b : ℤ} (hab : a + q = b) (y : L.X a) {i : ℤ} (hi : p + a = i) :
    (((w.curry.v p q hpq).hom x : Cochain L M q).v a b hab).hom y =
      (w.v i b (by omega)).hom ((ιTensorObj K L p a i hi).hom (x ⊗ₜ y)) := by
  subst hi
  rfl

/-- The component `x ⊗ y ↦ z(x)(y)` of the uncurried cochain on the summand `K^p ⊗ L^a`. -/
private def uncurryAux (z : Cochain K (linearHomComplex R L M) n) (p a j : ℤ)
    (h : p + a + n = j) : K.X p ⊗ L.X a ⟶ M.X j :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun x y => (((z.v p (p + n) rfl).hom x : Cochain L M (p + n)).v a j (by omega)).hom y)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)

/-- The uncurried form `x ⊗ y ↦ z(x)(y)` of a cochain `z` from `K` to the `R`-linear Hom complex
of `L` and `M`, a cochain of the same degree from `K ⊗ L` to `M`. -/
def uncurry (z : Cochain K (linearHomComplex R L M) n) : Cochain (K ⊗ L) M n :=
  Cochain.mk fun i j hij =>
    mapBifunctorDesc fun p a (h : p + a = i) => uncurryAux z p a j (by omega)

/-- The uncurried cochain evaluated on a pure tensor `x ⊗ y` is the original cochain evaluated on
`x` and then on `y`. -/
lemma uncurry_v_hom_ιTensorObj_apply (z : Cochain K (linearHomComplex R L M) n) {i j : ℤ}
    (hij : i + n = j) {p a : ℤ} (h : p + a = i) (x : K.X p) (y : L.X a) {q : ℤ}
    (hpq : p + n = q) :
    (z.uncurry.v i j hij).hom ((ιTensorObj K L p a i h).hom (x ⊗ₜ y)) =
      (((z.v p q hpq).hom x : Cochain L M q).v a j (by omega)).hom y := by
  subst hpq
  rw [← LinearMap.comp_apply (ModuleCat.Hom.hom (z.uncurry.v i j hij)), ← ModuleCat.hom_comp,
    uncurry, mk_v, ι_mapBifunctorDesc, uncurryAux, ModuleCat.MonoidalCategory.tensorLift_tmul]

@[simp]
lemma curry_uncurry (z : Cochain K (linearHomComplex R L M) n) : z.uncurry.curry = z :=
  ext_linearHomComplex fun p q hpq x a b hab y => by
    rw [curry_v_hom_apply_v_hom_apply _ hpq x hab y rfl,
      uncurry_v_hom_ιTensorObj_apply _ _ _ x y hpq]

@[simp]
lemma uncurry_curry (w : Cochain (K ⊗ L) M n) : w.curry.uncurry = w := by
  ext i j hij : 1
  refine mapBifunctor.hom_ext fun p a h => ModuleCat.MonoidalCategory.tensor_ext fun x y => ?_
  have h' : p + a = i := h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [uncurry_v_hom_ιTensorObj_apply _ _ h' x y rfl,
    curry_v_hom_apply_v_hom_apply _ rfl x _ y h']

variable (R K L M n) in
/-- Currying, as an `R`-linear equivalence between the cochains of degree `n` from `K ⊗ L` to `M`
and those from `K` to the `R`-linear Hom complex of `L` and `M`. -/
def curryLinearEquiv : Cochain (K ⊗ L) M n ≃ₗ[R] Cochain K (linearHomComplex R L M) n where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
  map_add' w w' := ext_linearHomComplex fun p q hpq x a b hab y => by
    simp [curry_v_hom_apply_v_hom_apply _ hpq x hab y rfl]
  map_smul' r w := ext_linearHomComplex fun p q hpq x a b hab y => by
    simp only [RingHom.id_apply, smul_linearHomComplex_v, ModuleCat.hom_smul, LinearMap.smul_apply,
      curry_v_hom_apply_v_hom_apply _ hpq x hab y rfl, Cochain.smul_v]

@[simp]
lemma curryLinearEquiv_apply (w : Cochain (K ⊗ L) M n) :
    curryLinearEquiv R K L M n w = w.curry := (rfl)

@[simp]
lemma curryLinearEquiv_symm_apply (z : Cochain K (linearHomComplex R L M) n) :
    (curryLinearEquiv R K L M n).symm z = z.uncurry := (rfl)

@[simp]
lemma curry_zero : (0 : Cochain (K ⊗ L) M n).curry = 0 :=
  (curryLinearEquiv R K L M n).map_zero

@[simp]
lemma uncurry_zero : (0 : Cochain K (linearHomComplex R L M) n).uncurry = 0 :=
  (curryLinearEquiv R K L M n).symm.map_zero

@[simp]
lemma curry_add (w w' : Cochain (K ⊗ L) M n) : (w + w').curry = w.curry + w'.curry :=
  (curryLinearEquiv R K L M n).map_add w w'

@[simp]
lemma uncurry_add (z z' : Cochain K (linearHomComplex R L M) n) :
    (z + z').uncurry = z.uncurry + z'.uncurry :=
  (curryLinearEquiv R K L M n).symm.map_add z z'

@[simp]
lemma curry_neg (w : Cochain (K ⊗ L) M n) : (-w).curry = -w.curry :=
  (curryLinearEquiv R K L M n).map_neg w

@[simp]
lemma uncurry_neg (z : Cochain K (linearHomComplex R L M) n) : (-z).uncurry = -z.uncurry :=
  (curryLinearEquiv R K L M n).symm.map_neg z

@[simp]
lemma curry_sub (w w' : Cochain (K ⊗ L) M n) : (w - w').curry = w.curry - w'.curry :=
  (curryLinearEquiv R K L M n).map_sub w w'

@[simp]
lemma uncurry_sub (z z' : Cochain K (linearHomComplex R L M) n) :
    (z - z').uncurry = z.uncurry - z'.uncurry :=
  (curryLinearEquiv R K L M n).symm.map_sub z z'

@[simp]
lemma curry_smul (r : R) (w : Cochain (K ⊗ L) M n) : (r • w).curry = r • w.curry :=
  (curryLinearEquiv R K L M n).map_smul r w

@[simp]
lemma uncurry_smul (r : R) (z : Cochain K (linearHomComplex R L M) n) :
    (r • z).uncurry = r • z.uncurry :=
  (curryLinearEquiv R K L M n).symm.map_smul r z

@[simp]
lemma curry_zsmul (k : ℤ) (w : Cochain (K ⊗ L) M n) : (k • w).curry = k • w.curry :=
  map_zsmul (curryLinearEquiv R K L M n) k w

@[simp]
lemma uncurry_zsmul (k : ℤ) (z : Cochain K (linearHomComplex R L M) n) :
    (k • z).uncurry = k • z.uncurry :=
  map_zsmul (curryLinearEquiv R K L M n).symm k z

/-- Currying commutes with the differentials of the Hom complexes. -/
lemma δ_curry (w : Cochain (K ⊗ L) M n) (m : ℤ) : δ n m w.curry = (δ n m w).curry := by
  by_cases hnm : n + 1 = m
  swap
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm, curry_zero]
  -- Evaluate both sides on `x ∈ K^p` and `y ∈ L^a`.  The right side is
  -- `d_M (w (x ⊗ y)) + (-1)^m w (d (x ⊗ y))`; the left side is `d_M (w (x ⊗ y))`
  -- `+ (-1)^q w (x ⊗ d y) + (-1)^m w (d x ⊗ y)`, and `(-1)^q = (-1)^m (-1)^p` matches the
  -- Koszul sign of `d (x ⊗ y)`.
  refine ext_linearHomComplex fun p q hpq x a b hab y => ?_
  rw [curry_v_hom_apply_v_hom_apply _ hpq x hab y rfl,
    δ_v n m hnm w (p + a) b (by omega) (b - 1) (p + a + 1) rfl rfl,
    δ_v n m hnm w.curry p q hpq (p + n) (p + 1) (by omega) rfl]
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply]
  rw [linearHomComplex_d_hom_apply]
  dsimp only [linearHomComplex_X]
  rw [Cochain.add_v, zsmul_linearHomComplex_v,
    δ_v (p + n) q (by omega) _ a b hab (b - 1) (a + 1) (by omega) rfl]
  have hd := congr(ModuleCat.Hom.hom
    $(ιTensorObj_tensor_d' K L (rfl : p + a = p + a) rfl rfl rfl) (x ⊗ₜ y))
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply] at hd ⊢
  rw [hd, curry_v_hom_apply_v_hom_apply _ _ _ _ _ (rfl : p + a = p + a),
    curry_v_hom_apply_v_hom_apply _ _ _ _ _ (by omega : p + (a + 1) = p + a + 1),
    curry_v_hom_apply_v_hom_apply _ _ _ _ _ (by omega : p + 1 + a = p + a + 1),
    map_add, map_zsmul, smul_add, smul_smul, ← Units.val_mul, ← Int.negOnePow_add,
    show m + p = q by omega]
  abel

/-- Uncurrying commutes with the differentials of the Hom complexes. -/
lemma δ_uncurry (z : Cochain K (linearHomComplex R L M) n) (m : ℤ) :
    δ n m z.uncurry = (δ n m z).uncurry := by
  refine (curryLinearEquiv R K L M m).injective ?_
  simp only [curryLinearEquiv_apply, ← δ_curry, curry_uncurry]

section Naturality

variable {K' L' M' : CochainComplex (ModuleCat.{v} R) ℤ}

/-- Currying is natural in the first tensor factor. -/
lemma curry_ofHom_whiskerRight_comp (f : K' ⟶ K) (w : Cochain (K ⊗ L) M n) :
    ((Cochain.ofHom (f ▷ L)).comp w (zero_add n)).curry =
      (Cochain.ofHom f).comp w.curry (zero_add n) :=
  ext_linearHomComplex fun p q hpq x a b hab y => by
    simp only [curry_v_hom_apply_v_hom_apply _ _ _ _ _ rfl, zero_cochain_comp_v, ofHom_v,
      ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [← LinearMap.comp_apply (ModuleCat.Hom.hom ((f ▷ L).f (p + a))), ← ModuleCat.hom_comp,
      ι_whiskerRight, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply]

/-- Currying is natural in the second tensor factor, which becomes the source of the inner Hom
complex. -/
lemma curry_ofHom_whiskerLeft_comp (g : L' ⟶ L) (w : Cochain (K ⊗ L) M n) :
    ((Cochain.ofHom (K ◁ g)).comp w (zero_add n)).curry =
      w.curry.comp (Cochain.ofHom (TauCeti.linearHomComplexPrecomp R g M)) (add_zero n) :=
  ext_linearHomComplex fun p q hpq x a b hab y => by
    simp only [curry_v_hom_apply_v_hom_apply _ _ _ _ _ rfl, zero_cochain_comp_v,
      comp_zero_cochain_v, ofHom_v, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [TauCeti.linearHomComplexPrecomp_f_apply]
    simp only [curry_v_hom_apply_v_hom_apply _ _ _ _ _ rfl, zero_cochain_comp_v, ofHom_v,
      ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [← LinearMap.comp_apply (ModuleCat.Hom.hom ((K ◁ g).f (p + a))), ← ModuleCat.hom_comp,
      ι_whiskerLeft, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply]

/-- Currying is natural in the target, which becomes the target of the inner Hom complex. -/
lemma curry_comp_ofHom (w : Cochain (K ⊗ L) M n) (h : M ⟶ M') :
    (w.comp (Cochain.ofHom h) (add_zero n)).curry =
      w.curry.comp (Cochain.ofHom (TauCeti.linearHomComplexPostcomp R L h)) (add_zero n) :=
  ext_linearHomComplex fun p q hpq x a b hab y => by
    simp only [curry_v_hom_apply_v_hom_apply _ _ _ _ _ rfl, comp_zero_cochain_v, ofHom_v,
      ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [TauCeti.linearHomComplexPostcomp_f_apply]
    simp only [curry_v_hom_apply_v_hom_apply _ _ _ _ _ rfl, comp_zero_cochain_v, ofHom_v,
      ModuleCat.hom_comp, LinearMap.comp_apply]

end Naturality

end CochainComplex.HomComplex.Cochain

namespace TauCeti

open CochainComplex HomComplex

variable {R : Type v} [CommRing R] (K L M : CochainComplex (ModuleCat.{v} R) ℤ)

/-- **The Hom complex out of a tensor product.** Currying identifies the `R`-linear Hom complex
from `K ⊗ L` to `M` with the Hom complex from `K` to the `R`-linear Hom complex of `L` and `M`. -/
def linearHomComplexCurryIso :
    linearHomComplex R (K ⊗ L) M ≅ linearHomComplex R K (linearHomComplex R L M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Cochain.curryLinearEquiv R K L M n).toModuleIso)
    (fun n m _ => by
      ext (w : ModuleCat.of R (Cochain (K ⊗ L) M n))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
        ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
      rw [linearHomComplex_d_hom_apply, linearHomComplex_d_hom_apply,
        Cochain.curryLinearEquiv_apply, Cochain.curryLinearEquiv_apply]
      exact Cochain.δ_curry w m)

@[simp]
lemma linearHomComplexCurryIso_hom_f_apply (n : ℤ)
    (w : ModuleCat.of R (Cochain (K ⊗ L) M n)) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexCurryIso K L M).hom.f n) w) =
      (w.curry : ModuleCat.of R (Cochain K (linearHomComplex R L M) n)) :=
  (rfl)

@[simp]
lemma linearHomComplexCurryIso_inv_f_apply (n : ℤ)
    (z : ModuleCat.of R (Cochain K (linearHomComplex R L M) n)) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexCurryIso K L M).inv.f n) z) =
      (z.uncurry : ModuleCat.of R (Cochain (K ⊗ L) M n)) :=
  (rfl)

variable {K L M}

/-- The curried isomorphism is natural in the first tensor factor. -/
@[reassoc]
lemma linearHomComplexCurryIso_hom_naturality_fst {K' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K' ⟶ K) :
    linearHomComplexPrecomp R (f ▷ L) M ≫ (linearHomComplexCurryIso K' L M).hom =
      (linearHomComplexCurryIso K L M).hom ≫
        linearHomComplexPrecomp R f (linearHomComplex R L M) := by
  ext n (w : ModuleCat.of R (Cochain (K ⊗ L) M n))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply]
  rw [linearHomComplexPrecomp_f_apply, linearHomComplexCurryIso_hom_f_apply,
    linearHomComplexCurryIso_hom_f_apply, linearHomComplexPrecomp_f_apply]
  exact Cochain.curry_ofHom_whiskerRight_comp f w

/-- The curried isomorphism is natural in the second tensor factor. -/
@[reassoc]
lemma linearHomComplexCurryIso_hom_naturality_snd {L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (g : L' ⟶ L) :
    linearHomComplexPrecomp R (K ◁ g) M ≫ (linearHomComplexCurryIso K L' M).hom =
      (linearHomComplexCurryIso K L M).hom ≫
        linearHomComplexPostcomp R K (linearHomComplexPrecomp R g M) := by
  ext n (w : ModuleCat.of R (Cochain (K ⊗ L) M n))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply]
  rw [linearHomComplexPrecomp_f_apply, linearHomComplexCurryIso_hom_f_apply,
    linearHomComplexCurryIso_hom_f_apply, linearHomComplexPostcomp_f_apply]
  exact Cochain.curry_ofHom_whiskerLeft_comp g w

/-- The curried isomorphism is natural in the target. -/
@[reassoc]
lemma linearHomComplexCurryIso_hom_naturality_target {M' : CochainComplex (ModuleCat.{v} R) ℤ}
    (h : M ⟶ M') :
    linearHomComplexPostcomp R (K ⊗ L) h ≫ (linearHomComplexCurryIso K L M').hom =
      (linearHomComplexCurryIso K L M).hom ≫
        linearHomComplexPostcomp R K (linearHomComplexPostcomp R L h) := by
  ext n (w : ModuleCat.of R (Cochain (K ⊗ L) M n))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply]
  rw [linearHomComplexPostcomp_f_apply, linearHomComplexCurryIso_hom_f_apply,
    linearHomComplexCurryIso_hom_f_apply, linearHomComplexPostcomp_f_apply]
  exact Cochain.curry_comp_ofHom w h

variable (K L M)

/-- **Tensor–Hom adjunction for complexes of modules.** Morphisms of complexes `K ⊗ L ⟶ M`
correspond to morphisms `K ⟶ Hom(L, M)` into the `R`-linear Hom complex, by currying the
associated degree-zero cocycles. -/
def linearHomComplexHomEquiv : (K ⊗ L ⟶ M) ≃ (K ⟶ linearHomComplex R L M) where
  toFun f := Cocycle.homOf (Cocycle.mk (Cochain.ofHom f).curry 1 (zero_add 1)
    (by rw [Cochain.δ_curry, δ_ofHom, Cochain.curry_zero]))
  invFun g := Cocycle.homOf (Cocycle.mk (Cochain.ofHom g).uncurry 1 (zero_add 1)
    (by rw [Cochain.δ_uncurry, δ_ofHom, Cochain.uncurry_zero]))
  left_inv f := Cochain.ofHom_injective (by simp)
  right_inv g := Cochain.ofHom_injective (by simp)

variable {K L M}

/-- The cocycle of `linearHomComplexHomEquiv f` is the curried cocycle of `f`. -/
@[simp]
lemma ofHom_linearHomComplexHomEquiv (f : K ⊗ L ⟶ M) :
    Cochain.ofHom (linearHomComplexHomEquiv K L M f) = (Cochain.ofHom f).curry := by
  simp [linearHomComplexHomEquiv]

/-- The cocycle of `(linearHomComplexHomEquiv K L M).symm g` is the uncurried cocycle of `g`. -/
@[simp]
lemma ofHom_linearHomComplexHomEquiv_symm (g : K ⟶ linearHomComplex R L M) :
    Cochain.ofHom ((linearHomComplexHomEquiv K L M).symm g) = (Cochain.ofHom g).uncurry := by
  simp [linearHomComplexHomEquiv]

/-- The curried morphism sends `x` of degree `p` to the cochain `y ↦ f (x ⊗ y)`. -/
@[simp]
lemma linearHomComplexHomEquiv_f_hom_apply_v_hom_apply (f : K ⊗ L ⟶ M) {p : ℤ} (x : K.X p)
    {a b : ℤ} (hab : a + p = b) (y : L.X a) :
    (dsimp% only [linearHomComplex_X]
      ((((linearHomComplexHomEquiv K L M f).f p).hom x : Cochain L M p).v a b hab).hom y) =
      (f.f b).hom ((ιTensorObj K L p a b (by omega)).hom (x ⊗ₜ y)) := by
  have h := Cochain.congr_v (ofHom_linearHomComplexHomEquiv f) p p (add_zero p)
  rw [Cochain.ofHom_v] at h
  rw [h, Cochain.curry_v_hom_apply_v_hom_apply _ _ _ _ _ (by omega : p + a = b), Cochain.ofHom_v]

/-- The uncurried morphism sends `x ⊗ y` to `g(x)(y)`. -/
@[simp]
lemma linearHomComplexHomEquiv_symm_f_hom_ιTensorObj_apply (g : K ⟶ linearHomComplex R L M)
    {p a i : ℤ} (h : p + a = i) (x : K.X p) (y : L.X a) :
    (((linearHomComplexHomEquiv K L M).symm g).f i).hom ((ιTensorObj K L p a i h).hom (x ⊗ₜ y)) =
      (((g.f p).hom x : Cochain L M p).v a i (by omega)).hom y := by
  have h' := Cochain.congr_v (ofHom_linearHomComplexHomEquiv_symm g) i i (add_zero i)
  rw [Cochain.ofHom_v] at h'
  rw [h', Cochain.uncurry_v_hom_ιTensorObj_apply _ _ h x y (add_zero p), Cochain.ofHom_v]

@[simp]
lemma linearHomComplexHomEquiv_zero : linearHomComplexHomEquiv K L M 0 = 0 :=
  Cochain.ofHom_injective (by simp)

/-- Homotopies between morphisms `K ⊗ L ⟶ M` correspond to homotopies between their curried
forms `K ⟶ Hom(L, M)`. -/
def linearHomComplexHomEquivHomotopy (f g : K ⊗ L ⟶ M) :
    Homotopy f g ≃
      Homotopy (linearHomComplexHomEquiv K L M f) (linearHomComplexHomEquiv K L M g) :=
  (Cochain.equivHomotopy f g).trans <|
    (Equiv.subtypeEquiv (Cochain.curryLinearEquiv R K L M (-1)).toEquiv fun z => by
      simp only [LinearEquiv.coe_toEquiv, ofHom_linearHomComplexHomEquiv,
        Cochain.curryLinearEquiv_apply]
      rw [Cochain.δ_curry, ← Cochain.curryLinearEquiv_apply, ← Cochain.curryLinearEquiv_apply,
        ← Cochain.curryLinearEquiv_apply, ← map_add,
        (Cochain.curryLinearEquiv R K L M 0).injective.eq_iff]).trans
      (Cochain.equivHomotopy _ _).symm

/-- `linearHomComplexHomEquiv` is natural in the first tensor factor. -/
lemma linearHomComplexHomEquiv_naturality_left {K' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K' ⟶ K) (g : K ⊗ L ⟶ M) :
    linearHomComplexHomEquiv K' L M (f ▷ L ≫ g) = f ≫ linearHomComplexHomEquiv K L M g :=
  Cochain.ofHom_injective (by
    simp only [ofHom_linearHomComplexHomEquiv, Cochain.ofHom_comp,
      Cochain.curry_ofHom_whiskerRight_comp])

/-- `(linearHomComplexHomEquiv K L M).symm` is natural in the first tensor factor. -/
lemma linearHomComplexHomEquiv_symm_naturality_left {K' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K' ⟶ K) (g : K ⟶ linearHomComplex R L M) :
    (linearHomComplexHomEquiv K' L M).symm (f ≫ g) =
      f ▷ L ≫ (linearHomComplexHomEquiv K L M).symm g := by
  rw [Equiv.symm_apply_eq, linearHomComplexHomEquiv_naturality_left, Equiv.apply_symm_apply]

/-- `linearHomComplexHomEquiv` is natural in the target. -/
lemma linearHomComplexHomEquiv_naturality_right {M' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K ⊗ L ⟶ M) (g : M ⟶ M') :
    linearHomComplexHomEquiv K L M' (f ≫ g) =
      linearHomComplexHomEquiv K L M f ≫ linearHomComplexPostcomp R L g :=
  Cochain.ofHom_injective (by
    simp only [ofHom_linearHomComplexHomEquiv, Cochain.ofHom_comp, Cochain.curry_comp_ofHom])

variable (L)

/-- Tensoring on the right with `L` is left adjoint to the `R`-linear Hom complex out of `L`. -/
def tensorRightLinearHomComplexAdjunction :
    tensorRight L ⊣ (linearHomComplexFunctor R).obj (Opposite.op L) :=
  Adjunction.mkOfHomEquiv
    { homEquiv K M := linearHomComplexHomEquiv K L M
      homEquiv_naturality_left_symm f g := linearHomComplexHomEquiv_symm_naturality_left f g
      homEquiv_naturality_right f g := linearHomComplexHomEquiv_naturality_right f g }

@[simp]
lemma tensorRightLinearHomComplexAdjunction_homEquiv (K M : CochainComplex (ModuleCat.{v} R) ℤ) :
    (tensorRightLinearHomComplexAdjunction L).homEquiv K M = linearHomComplexHomEquiv K L M := by
  rw [tensorRightLinearHomComplexAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

variable {L}

/-- The `R`-linear Hom complex from a K-flat complex to a K-injective complex is K-injective. -/
instance isKInjective_linearHomComplex (I : CochainComplex (ModuleCat.{v} R) ℤ) [L.IsKFlat]
    [I.IsKInjective] : (linearHomComplex R L I).IsKInjective where
  nonempty_homotopy_zero {A} f hA := by
    have hAL : (A ⊗ L).Acyclic := fun i => (IsKFlat.acyclic_tensor A hA i).of_iso (β_ L A)
    obtain ⟨h⟩ := IsKInjective.nonempty_homotopy_zero
      ((linearHomComplexHomEquiv A L I).symm f) hAL
    exact ⟨(Homotopy.ofEq (by simp)).trans
      ((linearHomComplexHomEquivHomotopy _ _ h).trans (Homotopy.ofEq (by simp)))⟩

end TauCeti
