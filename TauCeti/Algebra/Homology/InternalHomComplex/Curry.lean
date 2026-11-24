/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import TauCeti.Algebra.Homology.InternalHomComplex.Basic
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential

/-!
# Currying into the internal Hom complex

Let `C` be a closed monoidal preadditive category with countable products, and let `K`, `L` and
`M` be cochain complexes in `C` such that the tensor product `K ⊗ L` exists. A cochain `w` of
degree `n` from `K ⊗ L` to `M` has components `w_{p,q} : K^p ⊗ L^q ⟶ M^{p+q+n}`. For each `q`,
the family `p ↦ (-1)^{pq} w_{p,q}` is a cochain of degree `q + n` from `K ⊗ L^q` to `M`, that is
(`CochainComplex.internalHomComplexHomEquiv`) a morphism `L^q ⟶ 𝓗om^{q+n}(K, M)`. This curries
`w` to a cochain of degree `n` from `L` to the internal Hom complex `𝓗om^•(K, M)`, and currying
is a bijection.

With Mathlib's differential `d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y` on `K ⊗ L` and Mathlib's
differential `δ` of cochains, the Koszul sign `(-1)^{pq}` is exactly what makes currying commute
with `δ` (`CochainComplex.HomComplex.Cochain.δ_curryInternalHom`). So currying is an isomorphism
of Hom complexes `Hom(K ⊗ L, M) ≅ Hom(L, 𝓗om^•(K, M))`, and on degree-zero cocycles it gives the
chain-level tensor-Hom bijection `(K ⊗ L ⟶ M) ≃ (L ⟶ 𝓗om^•(K, M))`
(`TauCeti.tensorObjInternalHomComplexHomEquiv`).

## Main definitions

* `CochainComplex.HomComplex.Cochain.curryInternalHom` and
  `CochainComplex.HomComplex.Cochain.uncurryInternalHom`, with the additive equivalence
  `CochainComplex.HomComplex.Cochain.curryInternalHomAddEquiv`.
* `TauCeti.tensorObjInternalHomComplexHomEquiv`: the bijection
  `(K ⊗ L ⟶ M) ≃ (L ⟶ 𝓗om^•(K, M))`.

## Main results

* `CochainComplex.HomComplex.Cochain.δ_curryInternalHom`: currying commutes with the
  differentials of the Hom complexes.
* `TauCeti.tensorObjInternalHomComplexHomEquiv_naturality_fst`,
  `TauCeti.tensorObjInternalHomComplexHomEquiv_naturality_snd` and
  `TauCeti.tensorObjInternalHomComplexHomEquiv_naturality_target`: naturality in `K`, `L` and `M`.

## Implementation notes

This file is the closed monoidal analogue of `TauCeti/Algebra/Homology/LinearHomComplex/Curry.lean`
and follows its structure: currying of cochains, uncurrying through `mapBifunctorDesc`,
compatibility with `δ`, naturality, and the bijection on degree-zero cocycles built with
`CochainComplex.HomComplex.Cocycle.homOf`. Here the curried variable is the first tensor factor and
the Koszul sign `(-1)^{pq}` replaces the unsigned currying of complexes of modules. The
differential of `HomologicalComplex.tensorObj K L` on a summand is
`HomologicalComplex.ιTensorObj_d`.

## References

* [Stacks Project, Lemma 15.73.1 (0A5Y)](https://stacks.math.columbia.edu/tag/0A5Y): the
  tensor-Hom adjunction for the Hom complexes of complexes of modules.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalClosed HomologicalComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]

namespace CochainComplex

variable {K L : CochainComplex C ℤ} [HasTensor K L]

namespace HomComplex.Cochain

variable [MonoidalClosed C] [HasCountableProducts C] {M : CochainComplex C ℤ} {n : ℤ}

/-- For a fixed degree `q` of `L`, the cochain `p ↦ (-1)^{pq} w_{p,q}` of degree `r = q + n` from
`K ⊗ L^q` to `M` attached to a cochain `w` of degree `n` from `K ⊗ L` to `M`. -/
private def curryInternalHomAux (w : Cochain (tensorObj K L) M n) (q r : ℤ) (hqr : q + n = r) :
    Cochain (((tensorRight (L.X q)).mapHomologicalComplex _).obj K) M r :=
  Cochain.mk fun p s hps ↦
    (p * q).negOnePow • (ιTensorObj K L p q (p + q) rfl ≫ w.v (p + q) s (by omega))

/-- The curried form of a cochain `w` of degree `n` from `K ⊗ L` to `M`: the cochain of degree
`n` from `L` to the internal Hom complex `𝓗om^•(K, M)` whose component at `q` corresponds to the
cochain `p ↦ (-1)^{pq} w_{p,q}` from `K ⊗ L^q` to `M`. -/
def curryInternalHom (w : Cochain (tensorObj K L) M n) : Cochain L (internalHomComplex K M) n :=
  Cochain.mk fun q r hqr ↦
    (internalHomComplexHomEquiv K M (L.X q) r).symm (curryInternalHomAux w q r hqr)

/-- The component of the curried cochain on `K^p ⊗ L^q` is `(-1)^{pq} w_{p,q}`. -/
lemma internalHomComplexHomEquiv_curryInternalHom_v_v (w : Cochain (tensorObj K L) M n) {q r : ℤ}
    (hqr : q + n = r) {p s : ℤ} (hps : p + r = s) {i : ℤ} (hi : p + q = i) :
    (internalHomComplexHomEquiv K M (L.X q) r (w.curryInternalHom.v q r hqr)).v p s hps =
      (p * q).negOnePow • (ιTensorObj K L p q i hi ≫ w.v i s (by omega)) := by
  subst hi
  simp [curryInternalHom, curryInternalHomAux]

/-- The uncurried form of a cochain `z` of degree `n` from `L` to `𝓗om^•(K, M)`: the cochain of
degree `n` from `K ⊗ L` to `M` whose component on `K^p ⊗ L^q` is `(-1)^{pq}` times the component
at `p` of the cochain `K ⊗ L^q ⟶ M` corresponding to `z_q`. -/
def uncurryInternalHom (z : Cochain L (internalHomComplex K M) n) : Cochain (tensorObj K L) M n :=
  Cochain.mk fun i j hij ↦ mapBifunctorDesc fun p q (h : p + q = i) ↦
    (p * q).negOnePow • (internalHomComplexHomEquiv K M (L.X q) (q + n)
      (z.v q (q + n) rfl)).v p j (by omega)

/-- The component of the uncurried cochain on `K^p ⊗ L^q`. -/
lemma ιTensorObj_uncurryInternalHom_v (z : Cochain L (internalHomComplex K M) n) {i j : ℤ}
    (hij : i + n = j) {p q : ℤ} (h : p + q = i) {r : ℤ} (hqr : q + n = r) :
    ιTensorObj K L p q i h ≫ z.uncurryInternalHom.v i j hij =
      (p * q).negOnePow •
        (internalHomComplexHomEquiv K M (L.X q) r (z.v q r hqr)).v p j (by omega) := by
  subst hqr
  simp [uncurryInternalHom]

@[simp]
lemma curryInternalHom_uncurryInternalHom (z : Cochain L (internalHomComplex K M) n) :
    z.uncurryInternalHom.curryInternalHom = z := by
  ext q r hqr : 1
  refine (internalHomComplexHomEquiv K M (L.X q) r).injective ?_
  ext p s hps
  rw [internalHomComplexHomEquiv_curryInternalHom_v_v _ hqr hps rfl,
    ιTensorObj_uncurryInternalHom_v _ _ _ hqr, smul_smul, Int.units_mul_self, one_smul]

@[simp]
lemma uncurryInternalHom_curryInternalHom (w : Cochain (tensorObj K L) M n) :
    w.curryInternalHom.uncurryInternalHom = w := by
  ext i j hij : 1
  refine mapBifunctor.hom_ext fun p q h ↦ ?_
  rw [ιTensorObj_uncurryInternalHom_v _ _ _ rfl,
    internalHomComplexHomEquiv_curryInternalHom_v_v _ rfl _ h, smul_smul, Int.units_mul_self,
    one_smul]

variable (K L M n) in
/-- Currying, as an additive equivalence between the cochains of degree `n` from `K ⊗ L` to `M`
and those from `L` to the internal Hom complex `𝓗om^•(K, M)`. -/
def curryInternalHomAddEquiv :
    Cochain (tensorObj K L) M n ≃+ Cochain L (internalHomComplex K M) n where
  toFun := curryInternalHom
  invFun := uncurryInternalHom
  left_inv := uncurryInternalHom_curryInternalHom
  right_inv := curryInternalHom_uncurryInternalHom
  map_add' w w' := by
    ext q r hqr : 1
    refine (internalHomComplexHomEquiv K M (L.X q) r).injective ?_
    ext p s hps
    simp only [Cochain.add_v, map_add,
      internalHomComplexHomEquiv_curryInternalHom_v_v _ hqr hps rfl, Preadditive.comp_add, smul_add]

@[simp]
lemma curryInternalHomAddEquiv_apply (w : Cochain (tensorObj K L) M n) :
    curryInternalHomAddEquiv K L M n w = w.curryInternalHom :=
  (rfl)

@[simp]
lemma curryInternalHomAddEquiv_symm_apply (z : Cochain L (internalHomComplex K M) n) :
    (curryInternalHomAddEquiv K L M n).symm z = z.uncurryInternalHom :=
  (rfl)

@[simp]
lemma curryInternalHom_zero : (0 : Cochain (tensorObj K L) M n).curryInternalHom = 0 :=
  map_zero (curryInternalHomAddEquiv K L M n)

@[simp]
lemma uncurryInternalHom_zero : (0 : Cochain L (internalHomComplex K M) n).uncurryInternalHom = 0 :=
  map_zero (curryInternalHomAddEquiv K L M n).symm

omit [MonoidalPreadditive C] [MonoidalClosed C] [HasCountableProducts C] in
/-- The signs in `δ_curryInternalHom`: `(-1)^{q+m} (-1)^{(p+1)q} = (-1)^{pq} (-1)^m`. -/
private lemma negOnePow_add_mul_add_one_mul (p q m : ℤ) :
    (q + m).negOnePow * ((p + 1) * q).negOnePow = (p * q).negOnePow * m.negOnePow := by
  rw [← Int.negOnePow_add, ← Int.negOnePow_add, show q + m + (p + 1) * q = p * q + m + 2 * q by
    ring, Int.negOnePow_add _ (2 * q), Int.negOnePow_two_mul, mul_one]

omit [MonoidalPreadditive C] [MonoidalClosed C] [HasCountableProducts C] in
/-- The signs in `δ_curryInternalHom`: `(-1)^m (-1)^{p(q+1)} = (-1)^{pq} ((-1)^m (-1)^p)`. -/
private lemma negOnePow_mul_mul_add_one (p q m : ℤ) :
    m.negOnePow * (p * (q + 1)).negOnePow = (p * q).negOnePow * (m.negOnePow * p.negOnePow) := by
  rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add]
  congr 1
  ring

/-- Currying commutes with the differentials of the Hom complexes. -/
lemma δ_curryInternalHom (w : Cochain (tensorObj K L) M n) (m : ℤ) :
    δ n m w.curryInternalHom = (δ n m w).curryInternalHom := by
  by_cases hnm : n + 1 = m
  swap
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm, curryInternalHom_zero]
  ext q r hqr : 1
  refine (internalHomComplexHomEquiv K M (L.X q) r).injective ?_
  rw [δ_v n m hnm _ q r hqr (r - 1) (q + 1) rfl rfl, map_add, Units.smul_def, map_zsmul,
    internalHomComplexHomEquiv_comp_d, internalHomComplexHomEquiv_comp]
  ext p s hps
  rw [Cochain.add_v, Cochain.smul_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    δ_v (r - 1) r (by omega) _ p s hps (s - 1) (p + 1) rfl rfl,
    internalHomComplexHomEquiv_curryInternalHom_v_v _ _ _ (rfl : p + q = p + q),
    internalHomComplexHomEquiv_curryInternalHom_v_v _ _ _ (by omega : p + 1 + q = p + q + 1),
    internalHomComplexHomEquiv_curryInternalHom_v_v _ _ _ (by omega : p + (q + 1) = p + q + 1),
    internalHomComplexHomEquiv_curryInternalHom_v_v _ hqr hps (rfl : p + q = p + q),
    δ_v n m hnm w (p + q) s (by omega) (s - 1) (p + q + 1) rfl rfl]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Linear.comp_units_smul,
    Linear.units_smul_comp, Category.assoc, smul_add, smul_smul,
    ιTensorObj_d_assoc K L p q (p + q) rfl, ← Units.smul_def,
    Functor.mapHomologicalComplex_obj_d, NatTrans.mapHomologicalComplex_app_f,
    Functor.flip_map_app, curriedTensor_obj_map, Functor.flip_obj_map, curriedTensor_map_app]
  subst hqr
  rw [negOnePow_add_mul_add_one_mul, negOnePow_mul_mul_add_one, add_assoc]

/-- Uncurrying commutes with the differentials of the Hom complexes. -/
lemma δ_uncurryInternalHom (z : Cochain L (internalHomComplex K M) n) (m : ℤ) :
    δ n m z.uncurryInternalHom = (δ n m z).uncurryInternalHom := by
  refine (curryInternalHomAddEquiv K L M m).injective ?_
  simp only [curryInternalHomAddEquiv_apply, ← δ_curryInternalHom,
    curryInternalHom_uncurryInternalHom]

section Naturality

/-- Currying is natural in the target `M`. -/
lemma curryInternalHom_comp_ofHom {M' : CochainComplex C ℤ} (w : Cochain (tensorObj K L) M n)
    (h : M ⟶ M') :
    (w.comp (Cochain.ofHom h) (add_zero n)).curryInternalHom =
      w.curryInternalHom.comp (Cochain.ofHom (TauCeti.internalHomComplexPostcomp K h))
        (add_zero n) := by
  ext q r hqr : 1
  refine (internalHomComplexHomEquiv K M' (L.X q) r).injective ?_
  ext p s hps
  simp [TauCeti.internalHomComplexHomEquiv_comp_postcomp_f,
    internalHomComplexHomEquiv_curryInternalHom_v_v _ hqr hps rfl]

/-- Currying is natural in the second tensor factor `L`, which becomes the source. -/
lemma curryInternalHom_ofHom_id_tensorHom_comp {L' : CochainComplex C ℤ} [HasTensor K L']
    (g : L' ⟶ L) (w : Cochain (tensorObj K L) M n) :
    ((Cochain.ofHom (tensorHom (𝟙 K) g)).comp w (zero_add n)).curryInternalHom =
      (Cochain.ofHom g).comp w.curryInternalHom (zero_add n) := by
  ext q r hqr : 1
  refine (internalHomComplexHomEquiv K M (L'.X q) r).injective ?_
  ext p s hps
  simp [internalHomComplexHomEquiv_comp,
    internalHomComplexHomEquiv_curryInternalHom_v_v _ hqr hps rfl, ι_mapBifunctorMap_assoc]

/-- Currying is natural in the first tensor factor `K`, which becomes the source of the internal
Hom complex. -/
lemma curryInternalHom_ofHom_tensorHom_id_comp {K' : CochainComplex C ℤ} [HasTensor K' L]
    (f : K' ⟶ K) (w : Cochain (tensorObj K L) M n) :
    ((Cochain.ofHom (tensorHom f (𝟙 L))).comp w (zero_add n)).curryInternalHom =
      w.curryInternalHom.comp (Cochain.ofHom (TauCeti.internalHomComplexPrecomp f M))
        (add_zero n) := by
  ext q r hqr : 1
  refine (internalHomComplexHomEquiv K' M (L.X q) r).injective ?_
  ext p s hps
  simp [TauCeti.internalHomComplexHomEquiv_comp_precomp_f,
    internalHomComplexHomEquiv_curryInternalHom_v_v _ hqr hps rfl, ι_mapBifunctorMap_assoc]

end Naturality

end HomComplex.Cochain

end CochainComplex

namespace TauCeti

open CochainComplex HomComplex

variable [MonoidalClosed C] [HasCountableProducts C] (K L : CochainComplex C ℤ) [HasTensor K L]
  (M : CochainComplex C ℤ)

/-- **Chain-level tensor-Hom adjunction.** Morphisms of cochain complexes `K ⊗ L ⟶ M` correspond
to morphisms `L ⟶ 𝓗om^•(K, M)` into the internal Hom complex, by currying the associated
degree-zero cocycles with the Koszul sign `(-1)^{pq}` on `K^p ⊗ L^q`. -/
def tensorObjInternalHomComplexHomEquiv :
    (tensorObj K L ⟶ M) ≃ (L ⟶ internalHomComplex K M) where
  toFun f := Cocycle.homOf (Cocycle.mk (Cochain.ofHom f).curryInternalHom 1 (zero_add 1)
    (by rw [Cochain.δ_curryInternalHom, δ_ofHom, Cochain.curryInternalHom_zero]))
  invFun g := Cocycle.homOf (Cocycle.mk (Cochain.ofHom g).uncurryInternalHom 1 (zero_add 1)
    (by rw [Cochain.δ_uncurryInternalHom, δ_ofHom, Cochain.uncurryInternalHom_zero]))
  left_inv f := Cochain.ofHom_injective (by simp)
  right_inv g := Cochain.ofHom_injective (by simp)

variable {K L M}

/-- The cocycle of `tensorObjInternalHomComplexHomEquiv K L M f` is the curried cocycle of `f`. -/
@[simp]
lemma ofHom_tensorObjInternalHomComplexHomEquiv (f : tensorObj K L ⟶ M) :
    Cochain.ofHom (tensorObjInternalHomComplexHomEquiv K L M f) =
      (Cochain.ofHom f).curryInternalHom := by
  simp [tensorObjInternalHomComplexHomEquiv]

/-- The cocycle of `(tensorObjInternalHomComplexHomEquiv K L M).symm g` is the uncurried cocycle
of `g`. -/
@[simp]
lemma ofHom_tensorObjInternalHomComplexHomEquiv_symm (g : L ⟶ internalHomComplex K M) :
    Cochain.ofHom ((tensorObjInternalHomComplexHomEquiv K L M).symm g) =
      (Cochain.ofHom g).uncurryInternalHom := by
  simp [tensorObjInternalHomComplexHomEquiv]

/-- The component of the curried morphism at `q` corresponds to the cochain
`p ↦ (-1)^{pq} f_{p,q}` from `K ⊗ L^q` to `M`. -/
@[simp]
lemma internalHomComplexHomEquiv_tensorObjInternalHomComplexHomEquiv_f_v
    (f : tensorObj K L ⟶ M) (q : ℤ) {p s : ℤ} (hps : p + q = s) :
    (internalHomComplexHomEquiv K M (L.X q) q
      ((tensorObjInternalHomComplexHomEquiv K L M f).f q)).v p s hps =
      (p * q).negOnePow • (ιTensorObj K L p q s hps ≫ f.f s) := by
  have h := Cochain.congr_v (ofHom_tensorObjInternalHomComplexHomEquiv f) q q (add_zero q)
  rw [Cochain.ofHom_v] at h
  rw [h, Cochain.internalHomComplexHomEquiv_curryInternalHom_v_v _ _ hps hps, Cochain.ofHom_v]

/-- The component of the uncurried morphism on `K^p ⊗ L^q` is `(-1)^{pq}` times the component at
`p` of the cochain from `K ⊗ L^q` to `M` corresponding to `g_q`. -/
@[simp]
lemma ιTensorObj_tensorObjInternalHomComplexHomEquiv_symm_f (g : L ⟶ internalHomComplex K M)
    {p q s : ℤ} (hps : p + q = s) :
    ιTensorObj K L p q s hps ≫ ((tensorObjInternalHomComplexHomEquiv K L M).symm g).f s =
      (p * q).negOnePow • (internalHomComplexHomEquiv K M (L.X q) q (g.f q)).v p s hps := by
  have h := Cochain.congr_v (ofHom_tensorObjInternalHomComplexHomEquiv_symm g) s s (add_zero s)
  rw [Cochain.ofHom_v] at h
  rw [h, Cochain.ιTensorObj_uncurryInternalHom_v _ _ hps (add_zero q), Cochain.ofHom_v]

/-- `tensorObjInternalHomComplexHomEquiv` is natural in the target. -/
lemma tensorObjInternalHomComplexHomEquiv_naturality_target {M' : CochainComplex C ℤ}
    (f : tensorObj K L ⟶ M) (h : M ⟶ M') :
    tensorObjInternalHomComplexHomEquiv K L M' (f ≫ h) =
      tensorObjInternalHomComplexHomEquiv K L M f ≫ internalHomComplexPostcomp K h :=
  Cochain.ofHom_injective (by
    simp only [ofHom_tensorObjInternalHomComplexHomEquiv, Cochain.ofHom_comp,
      Cochain.curryInternalHom_comp_ofHom])

/-- `tensorObjInternalHomComplexHomEquiv` is natural in the second tensor factor. -/
lemma tensorObjInternalHomComplexHomEquiv_naturality_snd {L' : CochainComplex C ℤ}
    [HasTensor K L'] (g : L' ⟶ L) (f : tensorObj K L ⟶ M) :
    tensorObjInternalHomComplexHomEquiv K L' M (tensorHom (𝟙 K) g ≫ f) =
      g ≫ tensorObjInternalHomComplexHomEquiv K L M f :=
  Cochain.ofHom_injective (by
    simp only [ofHom_tensorObjInternalHomComplexHomEquiv, Cochain.ofHom_comp,
      Cochain.curryInternalHom_ofHom_id_tensorHom_comp])

/-- `tensorObjInternalHomComplexHomEquiv` is natural in the first tensor factor, which becomes
the source of the internal Hom complex. -/
lemma tensorObjInternalHomComplexHomEquiv_naturality_fst {K' : CochainComplex C ℤ}
    [HasTensor K' L] (f' : K' ⟶ K) (f : tensorObj K L ⟶ M) :
    tensorObjInternalHomComplexHomEquiv K' L M (tensorHom f' (𝟙 L) ≫ f) =
      tensorObjInternalHomComplexHomEquiv K L M f ≫ internalHomComplexPrecomp f' M :=
  Cochain.ofHom_injective (by
    simp only [ofHom_tensorObjInternalHomComplexHomEquiv, Cochain.ofHom_comp,
      Cochain.curryInternalHom_ofHom_tensorHom_id_comp])

end TauCeti

end
