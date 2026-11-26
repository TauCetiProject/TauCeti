/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.Regrade
public import TauCeti.Algebra.Homology.LinearHomComplex.Bidual
public import TauCeti.Algebra.Homology.LinearHomComplex.ChainDual

/-!
# Regrading dual complexes

For an integer `n`, a chain complex `K` of modules indexed by `ℤ` (differential of degree `-1`) is
regraded into the cochain complex `C` with `C^k = K_(n-k)` and the same differential
(`ChainComplex.regradeEquivalence`). This is the passage from the raw homological grading of a
Hamiltonian Floer complex `CF_*` to its cohomological grading `C^k = CF_(n-k)`. This file compares
the two ways of forming linear duals: in the raw grading and in the cochain grading.

**The dual of a chain complex.** The dual `K∨` of a chain complex `K` of `R`-modules
(`ChainComplex.linearDual`) has in degree `p` the linear forms on `K_(-p)`, with the sign
convention of the dual of a cochain complex (`CochainComplex.linearDual`) in homological degrees.

**Duals and regrading.** The dual `C∨` of the regrading `C` of `K` by `n` has in degree `k` the
linear forms on `C^(-k) = K_(n + k)`; so has the regrading of `K∨` by `-n`, in degree `k` the
term `K∨_(-n - k)`. The two complexes are isomorphic
(`ChainComplex.regradeLinearDualIso`), but not by the identity on forms: the differential of `C∨`
in degree `k` is `(-1)^(k + 1) f ∘ d_K`, that of the regrading of `K∨` is
`(-1)^(-n - k + 1) f ∘ d_K`, and the two differ by `(-1)^n`. The isomorphism is the identity on
forms twisted by the sign `(-1)^(k n)` in degree `k` (`ChainComplex.regradeLinearDualIso_hom_f`),
as for the comparison `ChainComplex.regradeIsoShift` of the regrading with the shift. It is
natural in `K` (`ChainComplex.regradeLinearDualIso_hom_naturality`). For `n = 0` it identifies the
dual of a chain complex with the dual of the cochain complex `K^k = K_(0 - k)`, regraded back, with
no sign (`ChainComplex.linearDualIsoRegradeLinearDual`).

**Bidual maps and regrading.** The double dual `C∨∨` of the regrading is the regrading by `n` of
`K∨∨`: in degree `k` both consist of the forms on the forms on `K_(n-k)`, and the comparison
`ChainComplex.regradeBidualIso` identifies them without sign (`ChainComplex.regradeBidualXIso`);
both differentials are the double transpose of `d_K` with the sign `-1`. The chain-compatible
bidual maps `j(x) = (-1)^|x| (f ↦ f x)` of the two gradings do not correspond under it: in the raw
grading of `K` an element `x` of `K_(n-k)` has degree `n - k`, in the cochain grading of `C` it has
degree `k`, so the regrading of the bidual map of `K` is `(-1)^n` times the bidual map of `C`
(`ChainComplex.restrictionMap_bidualHom`).

For the Floer complex of a symplectic manifold of dimension `2n`, the external kernel of an
operation counts functionals on tensor products of the generators of the inputs with the duals of
those of the outputs. Its raw and cochain gradings, and the Koszul signs computed in each, are
related by this comparison together with the regrading of tensor products
(`ChainComplex.regradeTensorIso`): the dual of a generator of raw degree `μ` has raw degree `-μ`
and cochain degree `μ - n`. A count functional is read as an operator through the inverse of the
bidual map of the outputs (`TauCeti.linearHomComplexTensorDualIso`), so the readouts formed in the
two gradings differ by the sign `(-1)^n`.

## Main definitions and results

* `ChainComplex.regradeLinearDualXIso`: the identification, without sign, of the term of degree
  `k` of the dual of the regrading by `n` with the term of degree `-n - k` of the dual.
* `ChainComplex.regradeLinearDualIso`: the isomorphism between the dual of the regrading by `n`
  and the regrading by `-n` of the dual.
* `ChainComplex.linearDualIsoRegradeLinearDual`: the dual of a chain complex as the dual of its
  regrading by `0`, regraded back.
* `ChainComplex.regradeBidualIso`: the isomorphism between the double dual of the regrading by
  `n` and the regrading by `n` of the double dual.
* `ChainComplex.restrictionMap_bidualHom`: the regrading of the bidual map of `K` is `(-1)^n`
  times the bidual map of its regrading.

## References

* C. A. Weibel, *An introduction to homological algebra*, Section 2.7, on Hom complexes and
  their sign conventions.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex ComplexShape

universe u

namespace ChainComplex

variable {R : Type u} [CommRing R] {K L : ChainComplex (ModuleCat.{u} R) ℤ}

section Regrade

variable (n : ℤ) (K)

/-- The term of degree `k` of the dual of the regrading of `K` by `n`, the linear forms on
`K_(n + k)`, identified with the term of degree `-n - k` of `K∨`, the linear forms on
`K_(-(-n - k))`, by transport along `-(-n - k) = n + k`. This is the unsigned identification of
terms behind `ChainComplex.regradeLinearDualIso`. -/
def regradeLinearDualXIso (k : ℤ) :
    (CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n))).X k ≅
      (linearDual K).X (-n - k) :=
  ((CochainComplex.linearDualXEquiv _ (neg_add_cancel k)).trans
    (K.restrictionXIso _
      (show n - -k = -(-n - k) by omega)).toLinearEquiv.symm.dualMap).toModuleIso

/-- The identification `regradeLinearDualXIso` reads a form on `K_(n + k)` on `K_(-(-n - k))`.
It is not a simp lemma: simp rewrites the type `(linearDual K).X (-n - k)` of the form in its
left-hand side to the dual module. -/
theorem regradeLinearDualXIso_hom_apply (k : ℤ)
    (g : (CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n))).X k)
    (x : K.X (-(-n - k))) :
    (K.regradeLinearDualXIso n k).hom.hom g x =
      CochainComplex.linearDualXEquiv _ (neg_add_cancel k) g
        ((K.restrictionXIso _ (show n - -k = -(-n - k) by omega)).inv.hom x) :=
  (rfl)

/-- The inverse of `regradeLinearDualXIso` reads a form on `K_(-(-n - k))` on `K_(n + k)`. -/
theorem linearDualXEquiv_regradeLinearDualXIso_inv_apply (k : ℤ) (f : (linearDual K).X (-n - k))
    (y : (K.restriction (embeddingUpIntDownIntSub n)).X (-k)) :
    CochainComplex.linearDualXEquiv _ (neg_add_cancel k) ((K.regradeLinearDualXIso n k).inv.hom f)
      y = f ((K.restrictionXIso _ (show n - -k = -(-n - k) by omega)).hom.hom y) := by
  conv_rhs => rw [← (K.regradeLinearDualXIso n k).inv_hom_id_apply f,
    regradeLinearDualXIso_hom_apply]
  simp

/-- The signed identifications `regradeLinearDualXIso` commute with the differentials. -/
private theorem regradeLinearDualXIso_comm (k : ℤ) :
    ((k * n).negOnePow • (K.regradeLinearDualXIso n k).hom) ≫
        (linearDual K).d (-n - k) (-n - (k + 1)) =
      (CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n))).d k (k + 1) ≫
        (((k + 1) * n).negOnePow • (K.regradeLinearDualXIso n (k + 1)).hom) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun g ↦ LinearMap.ext fun x ↦ ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Units.smul_def, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_ofHom,
    LinearMap.dualMap_apply]
  -- Both sides evaluate `g` on the differential of `K` from `K_(n + k + 1)` to `K_(n + k)`.
  rw [regradeLinearDualXIso_hom_apply, regradeLinearDualXIso_hom_apply,
    CochainComplex.linearDualXEquiv_d_apply (neg_add_cancel k) (neg_add_cancel (k + 1)),
    restriction_d_eq _ _ (show n - -(k + 1) = -(-n - (k + 1)) by omega)
      (show n - -k = -(-n - k) by omega)]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Iso.inv_hom_id_apply, Units.smul_def,
    smul_smul]
  congr 1
  norm_cast
  rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨-n - k, by ring⟩

/-- **The dual of the regrading is the regrading of the dual.** For a chain complex `K` and an
integer `n`, the dual of the regrading `C^k = K_(n-k)` of `K` by `n` is isomorphic to the
regrading of `K∨` by `-n`. In degree `k` both consist of the linear forms on `K_(n + k)`, and the
isomorphism is the identity on forms twisted by the sign `(-1)^(k n)`
(`ChainComplex.regradeLinearDualIso_hom_f`). -/
def regradeLinearDualIso :
    CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n)) ≅
      (linearDual K).restriction (embeddingUpIntDownIntSub (-n)) :=
  Hom.isoOfComponents (fun k ↦ (k * n).negOnePow • (K.regradeLinearDualXIso n k ≪≫
      ((linearDual K).restrictionXIso (embeddingUpIntDownIntSub (-n)) (i := k) (i' := -n - k)
        rfl).symm))
    (fun k l hkl ↦ by
      obtain rfl : k + 1 = l := hkl
      rw [restriction_d_eq _ _ (i' := -n - k) (j' := -n - (k + 1)) rfl rfl]
      have h := regradeLinearDualXIso_comm K n k =≫ ((linearDual K).restrictionXIso
        (embeddingUpIntDownIntSub (-n)) (i := k + 1) (i' := -n - (k + 1)) rfl).inv
      simp only [Category.assoc] at h
      simpa only [Preadditive.smul_iso_hom, Iso.trans_hom, Iso.symm_hom, Linear.units_smul_comp,
        Linear.comp_units_smul, Category.assoc, Iso.inv_hom_id_assoc] using h)

/-- In degree `k`, the comparison `regradeLinearDualIso` is the identification
`regradeLinearDualXIso`, read in degree `k` of the regrading of `K∨`, twisted by the sign
`(-1)^(k n)`. -/
@[simp]
theorem regradeLinearDualIso_hom_f (k : ℤ) :
    (K.regradeLinearDualIso n).hom.f k = (k * n).negOnePow • ((K.regradeLinearDualXIso n k).hom ≫
      ((linearDual K).restrictionXIso (embeddingUpIntDownIntSub (-n)) (i := k) (i' := -n - k)
        rfl).inv) :=
  (rfl)

/-- In degree `k`, the inverse of `regradeLinearDualIso` is the inverse of the identification
`regradeLinearDualXIso`, read in degree `k` of the regrading of `K∨`, twisted by the sign
`(-1)^(k n)`. -/
@[simp]
theorem regradeLinearDualIso_inv_f (k : ℤ) :
    (K.regradeLinearDualIso n).inv.f k = (k * n).negOnePow •
      (((linearDual K).restrictionXIso (embeddingUpIntDownIntSub (-n)) (i := k) (i' := -n - k)
        rfl).hom ≫ (K.regradeLinearDualXIso n k).inv) := by
  simp only [regradeLinearDualIso, Hom.isoOfComponents_inv_f, Preadditive.smul_iso_inv,
    Int.units_inv_eq_self, Iso.trans_inv, Iso.symm_inv]

/-- **The comparison on forms.** The comparison `regradeLinearDualIso` sends a form `g` on
`K_(n + k)` to the same form, read on `K_(-(-n - k))`, twisted by the sign `(-1)^(k n)`. It is not
a simp lemma: simp first rewrites the component by `regradeLinearDualIso_hom_f`. -/
theorem restrictionXIso_hom_regradeLinearDualIso_hom_f_apply (k : ℤ)
    (g : (CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n))).X k)
    (x : K.X (-(-n - k))) :
    ((linearDual K).restrictionXIso (embeddingUpIntDownIntSub (-n)) (i := k) (i' := -n - k)
        rfl).hom.hom (((K.regradeLinearDualIso n).hom.f k).hom g) x =
      (k * n).negOnePow • CochainComplex.linearDualXEquiv _ (neg_add_cancel k) g
        ((K.restrictionXIso _ (show n - -k = -(-n - k) by omega)).inv.hom x) := by
  simp only [regradeLinearDualIso_hom_f, Units.smul_def, ModuleCat.hom_zsmul, ModuleCat.hom_comp,
    LinearMap.smul_apply, LinearMap.comp_apply, map_zsmul, Iso.inv_hom_id_apply]
  rw [regradeLinearDualXIso_hom_apply]

/-- **The inverse comparison on forms.** The inverse of `regradeLinearDualIso` sends a form `f` on
`K_(-(-n - k))` to the same form, read on `K_(n + k)`, twisted by the sign `(-1)^(k n)`. It is not
a simp lemma: simp first rewrites the component by `regradeLinearDualIso_inv_f`. -/
theorem linearDualXEquiv_regradeLinearDualIso_inv_f_apply (k : ℤ)
    (f : ((linearDual K).restriction (embeddingUpIntDownIntSub (-n))).X k)
    (y : (K.restriction (embeddingUpIntDownIntSub n)).X (-k)) :
    CochainComplex.linearDualXEquiv _ (neg_add_cancel k)
        (((K.regradeLinearDualIso n).inv.f k).hom f) y =
      (k * n).negOnePow • ((linearDual K).restrictionXIso (embeddingUpIntDownIntSub (-n)) (i := k)
        (i' := -n - k) rfl).hom.hom f
          ((K.restrictionXIso _ (show n - -k = -(-n - k) by omega)).hom.hom y) := by
  simp only [regradeLinearDualIso_inv_f, Units.smul_def, ModuleCat.hom_zsmul, ModuleCat.hom_comp,
    LinearMap.smul_apply, LinearMap.comp_apply, map_zsmul]
  rw [linearDualXEquiv_regradeLinearDualXIso_inv_apply]

variable {K} in
/-- The identifications `regradeLinearDualXIso` intertwine the transposes of a morphism
`φ : K ⟶ L` and of its regrading. -/
@[reassoc]
private theorem regradeLinearDualXIso_naturality (φ : K ⟶ L) (k : ℤ) :
    (TauCeti.linearHomComplexPrecomp R (restrictionMap φ (embeddingUpIntDownIntSub n)) _).f k ≫
        (K.regradeLinearDualXIso n k).hom =
      (L.regradeLinearDualXIso n k).hom ≫ (linearDualMap φ).f (-n - k) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun g ↦ LinearMap.ext fun x ↦ ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [regradeLinearDualXIso_hom_apply, linearDualMap_f_apply, regradeLinearDualXIso_hom_apply,
    CochainComplex.linearDualXEquiv_linearHomComplexPrecomp_f_apply,
    restrictionMap_f' _ _ (show n - -k = -(-n - k) by omega)]
  simp

variable {K} in
/-- **Naturality.** The comparison `regradeLinearDualIso` intertwines the transposes of a
morphism `φ : K ⟶ L` and of its regrading. -/
@[reassoc]
theorem regradeLinearDualIso_hom_naturality (φ : K ⟶ L) :
    TauCeti.linearHomComplexPrecomp R (restrictionMap φ (embeddingUpIntDownIntSub n)) _ ≫
        (K.regradeLinearDualIso n).hom =
      (L.regradeLinearDualIso n).hom ≫
        restrictionMap (linearDualMap φ) (embeddingUpIntDownIntSub (-n)) := by
  ext k : 1
  rw [comp_f, comp_f, regradeLinearDualIso_hom_f, regradeLinearDualIso_hom_f,
    restrictionMap_f' _ _ (i' := -n - k) rfl]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    Iso.inv_hom_id_assoc, regradeLinearDualXIso_naturality_assoc]

variable {K} in
/-- **Naturality of the inverse.** The inverse of the comparison `regradeLinearDualIso`
intertwines the transposes of a morphism `φ : K ⟶ L` and of its regrading. -/
@[reassoc]
theorem regradeLinearDualIso_inv_naturality (φ : K ⟶ L) :
    restrictionMap (linearDualMap φ) (embeddingUpIntDownIntSub (-n)) ≫
        (K.regradeLinearDualIso n).inv =
      (L.regradeLinearDualIso n).inv ≫
        TauCeti.linearHomComplexPrecomp R (restrictionMap φ (embeddingUpIntDownIntSub n)) _ := by
  rw [Iso.comp_inv_eq, Category.assoc, regradeLinearDualIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- **The dual of a chain complex as the dual of a cochain complex.** The dual `K∨` of a chain
complex `K` is isomorphic to the dual of the cochain complex `K^k = K_(0 - k)`, the regrading of
`K` by `0`, regraded back into a chain complex. This is the case `n = 0` of
`regradeLinearDualIso`, whose sign `(-1)^(k n)` is then trivial, composed with the unit of
`regradeEquivalence`. -/
def linearDualIsoRegradeLinearDual :
    linearDual K ≅ (regradeEquivalence (ModuleCat.{u} R) 0).inverse.obj
      (CochainComplex.linearDual R ((regradeEquivalence (ModuleCat.{u} R) 0).functor.obj K)) :=
  (regradeEquivalence (ModuleCat.{u} R) 0).unitIso.app (linearDual K) ≪≫
    (regradeEquivalence (ModuleCat.{u} R) 0).inverse.mapIso
      (K.regradeLinearDualIso 0).symm

/-- In degree `p`, the isomorphism `linearDualIsoRegradeLinearDual` is the inverse of the comparison
`regradeLinearDualIso` for `n = 0` in degree `0 - p`, after the identification `p = 0 - (0 - p)`. -/
@[simp]
theorem linearDualIsoRegradeLinearDual_hom_f (p : ℤ) :
    K.linearDualIsoRegradeLinearDual.hom.f p =
      ((linearDual K).XIsoOfEq (show p = 0 - (0 - p) by omega)).hom ≫
        (K.regradeLinearDualIso 0).inv.f (0 - p) :=
  (rfl)

/-- The term of degree `k` of the double dual of the regrading of `K` by `n`, the forms on the
forms on `K_(n - k)`, identified with the term of degree `n - k` of `K∨∨`, the forms on the forms
on `K_(-(-(n - k)))`, by transport along `n - k = -(-(n - k))`. This is the unsigned identification
of terms behind `ChainComplex.regradeBidualIso`. -/
def regradeBidualXIso (k : ℤ) :
    (CochainComplex.linearDual R
        (CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n)))).X k ≅
      (linearDual (linearDual K)).X (n - k) :=
  ((CochainComplex.linearDualXEquiv _ (neg_add_cancel k)).trans
    ((K.restrictionXIso _ ((embeddingUpIntDownIntSub_f n k).trans
      (neg_neg (n - k)).symm)).toLinearEquiv.dualMap.trans
        (CochainComplex.linearDualXEquiv _ (add_neg_cancel k)).symm).dualMap).toModuleIso

/-- The identification `regradeBidualXIso` evaluates a form `y` on the forms on `K_(n - k)` at the
form `f` on `K_(-(-(n - k)))`, read on `K_(n - k)`. -/
theorem regradeBidualXIso_hom_apply (k : ℤ)
    (y : (CochainComplex.linearDual R
      (CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n)))).X k)
    (f : (linearDual K).X (-(n - k))) :
    (K.regradeBidualXIso n k).hom.hom y f =
      CochainComplex.linearDualXEquiv _ (neg_add_cancel k) y
        ((CochainComplex.linearDualXEquiv _ (add_neg_cancel k)).symm
          (f ∘ₗ (K.restrictionXIso _ ((embeddingUpIntDownIntSub_f n k).trans
            (neg_neg (n - k)).symm)).hom.hom)) :=
  (rfl)

/-- The inverse of `regradeBidualXIso` evaluates a form `z` on the forms on `K_(-(-(n - k)))` at
the form `g` on `K_(n - k)`, read on `K_(-(-(n - k)))`. -/
theorem linearDualXEquiv_regradeBidualXIso_inv_apply (k : ℤ)
    (z : (linearDual (linearDual K)).X (n - k))
    (g : (CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n))).X (-k)) :
    CochainComplex.linearDualXEquiv _ (neg_add_cancel k) ((K.regradeBidualXIso n k).inv.hom z) g =
      z (CochainComplex.linearDualXEquiv _ (add_neg_cancel k) g ∘ₗ
        (K.restrictionXIso _ ((embeddingUpIntDownIntSub_f n k).trans
          (neg_neg (n - k)).symm)).inv.hom) := by
  conv_rhs => rw [← (K.regradeBidualXIso n k).inv_hom_id_apply z, regradeBidualXIso_hom_apply,
    LinearMap.comp_assoc, ← ModuleCat.hom_comp, Iso.hom_inv_id, ModuleCat.hom_id,
    LinearMap.comp_id, LinearEquiv.symm_apply_apply]

/-- The identifications `regradeBidualXIso` commute with the differentials. -/
private theorem regradeBidualXIso_comm (k : ℤ) :
    (K.regradeBidualXIso n k).hom ≫ (linearDual (linearDual K)).d (n - k) (n - (k + 1)) =
      (CochainComplex.linearDual R
        (CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n)))).d k (k + 1) ≫
        (K.regradeBidualXIso n (k + 1)).hom := by
  ext y f
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Units.smul_def, ModuleCat.hom_zsmul,
    LinearMap.smul_apply, ModuleCat.hom_ofHom, LinearMap.dualMap_apply, map_zsmul]
  rw [regradeBidualXIso_hom_apply, regradeBidualXIso_hom_apply,
    CochainComplex.linearDualXEquiv_d_apply (neg_add_cancel k) (neg_add_cancel (k + 1))]
  -- The transpose of the differential of the regrading, read on forms on `K`, is the transpose of
  -- the differential of `K` twisted by the sign `(-1)^k` of the dual of a cochain complex.
  have key : ((CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n))).d
        (-(k + 1)) (-k)).hom ((CochainComplex.linearDualXEquiv _ (add_neg_cancel (k + 1))).symm
          (f ∘ₗ (K.restrictionXIso _ ((embeddingUpIntDownIntSub_f n (k + 1)).trans
            (neg_neg _).symm)).hom.hom)) =
      (-k).negOnePow • (CochainComplex.linearDualXEquiv _ (add_neg_cancel k)).symm
        ((K.d (-(-(n - k))) (-(-(n - (k + 1))))).hom.dualMap f ∘ₗ
          (K.restrictionXIso _ ((embeddingUpIntDownIntSub_f n k).trans
            (neg_neg (n - k)).symm)).hom.hom) := by
    refine (CochainComplex.linearDualXEquiv _ (add_neg_cancel k)).injective
      (LinearMap.ext fun x ↦ ?_)
    rw [CochainComplex.linearDualXEquiv_d_apply (add_neg_cancel (k + 1)) (add_neg_cancel k),
      restriction_d_eq _ _ ((embeddingUpIntDownIntSub_f n k).trans (neg_neg (n - k)).symm)
        ((embeddingUpIntDownIntSub_f n (k + 1)).trans (neg_neg _).symm)]
    simp
  rw [key]
  simp only [map_zsmul_unit, smul_smul]
  -- The two signs of the dual differentials of `K∨∨` against those of `C∨∨`.
  congr 1
  norm_cast
  rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨1, by omega⟩

/-- **The double dual of the regrading is the regrading of the double dual.** For a chain complex
`K` and an integer `n`, the double dual of the regrading `C^k = K_(n-k)` of `K` by `n` is
isomorphic to the regrading of `K∨∨` by `n`. In degree `k` both consist of the forms on the forms
on `K_(n - k)`, and the isomorphism is the identity on them, without sign
(`ChainComplex.regradeBidualIso_hom_f`, `ChainComplex.regradeBidualXIso_hom_apply`). -/
def regradeBidualIso :
    CochainComplex.linearDual R
        (CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n))) ≅
      (linearDual (linearDual K)).restriction (embeddingUpIntDownIntSub n) :=
  Hom.isoOfComponents (fun k ↦ K.regradeBidualXIso n k ≪≫
      ((linearDual (linearDual K)).restrictionXIso (embeddingUpIntDownIntSub n)
        (embeddingUpIntDownIntSub_f n k)).symm)
    (fun k l hkl ↦ by
      obtain rfl : k + 1 = l := hkl
      rw [restriction_d_eq _ _ (embeddingUpIntDownIntSub_f n k)
        (embeddingUpIntDownIntSub_f n (k + 1))]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, regradeBidualXIso_comm, Category.assoc])

/-- In degree `k`, the comparison `regradeBidualIso` is the identification `regradeBidualXIso`,
read in degree `k` of the regrading of `K∨∨`. -/
@[simp]
theorem regradeBidualIso_hom_f (k : ℤ) :
    (K.regradeBidualIso n).hom.f k = (K.regradeBidualXIso n k).hom ≫
      ((linearDual (linearDual K)).restrictionXIso (embeddingUpIntDownIntSub n)
        (embeddingUpIntDownIntSub_f n k)).inv :=
  (rfl)

/-- In degree `k`, the inverse of `regradeBidualIso` is the inverse of the identification
`regradeBidualXIso`, read in degree `k` of the regrading of `K∨∨`. -/
@[simp]
theorem regradeBidualIso_inv_f (k : ℤ) :
    (K.regradeBidualIso n).inv.f k =
      ((linearDual (linearDual K)).restrictionXIso (embeddingUpIntDownIntSub n)
        (embeddingUpIntDownIntSub_f n k)).hom ≫ (K.regradeBidualXIso n k).inv :=
  (rfl)

/-- **The comparison on double duals.** The comparison `regradeBidualIso` sends a form `y` on the
forms on `K_(n - k)` to the form evaluating `y` at a form `f` on `K_(-(-(n - k)))`, read on
`K_(n - k)`, without sign. It is not a simp lemma: simp first rewrites the component by
`regradeBidualIso_hom_f`. -/
theorem restrictionXIso_hom_regradeBidualIso_hom_f_apply (k : ℤ)
    (y : (CochainComplex.linearDual R
      (CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n)))).X k)
    (f : (linearDual K).X (-(n - k))) :
    ((linearDual (linearDual K)).restrictionXIso (embeddingUpIntDownIntSub n)
        (embeddingUpIntDownIntSub_f n k)).hom.hom (((K.regradeBidualIso n).hom.f k).hom y) f =
      CochainComplex.linearDualXEquiv _ (neg_add_cancel k) y
        ((CochainComplex.linearDualXEquiv _ (add_neg_cancel k)).symm
          (f ∘ₗ (K.restrictionXIso _ ((embeddingUpIntDownIntSub_f n k).trans
            (neg_neg (n - k)).symm)).hom.hom)) := by
  simp only [regradeBidualIso_hom_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    Iso.inv_hom_id_apply]
  rw [regradeBidualXIso_hom_apply]

/-- **The inverse comparison on double duals.** The inverse of `regradeBidualIso` sends a form `z`
on the forms on `K_(-(-(n - k)))` to the form evaluating `z` at a form `g` on `K_(n - k)`, read on
`K_(-(-(n - k)))`, without sign. It is not a simp lemma: simp first rewrites the component by
`regradeBidualIso_inv_f`. -/
theorem linearDualXEquiv_regradeBidualIso_inv_f_apply (k : ℤ)
    (z : ((linearDual (linearDual K)).restriction (embeddingUpIntDownIntSub n)).X k)
    (g : (CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n))).X (-k)) :
    CochainComplex.linearDualXEquiv _ (neg_add_cancel k)
        (((K.regradeBidualIso n).inv.f k).hom z) g =
      ((linearDual (linearDual K)).restrictionXIso (embeddingUpIntDownIntSub n)
        (embeddingUpIntDownIntSub_f n k)).hom.hom z
          (CochainComplex.linearDualXEquiv _ (add_neg_cancel k) g ∘ₗ
            (K.restrictionXIso _ ((embeddingUpIntDownIntSub_f n k).trans
              (neg_neg (n - k)).symm)).inv.hom) := by
  simp only [regradeBidualIso_inv_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [linearDualXEquiv_regradeBidualXIso_inv_apply]

variable {K} in
/-- The identifications `regradeBidualXIso` intertwine the double transposes of a morphism
`φ : K ⟶ L` and of its regrading. -/
@[reassoc]
private theorem regradeBidualXIso_naturality (φ : K ⟶ L) (k : ℤ) :
    (TauCeti.linearHomComplexPrecomp R (TauCeti.linearHomComplexPrecomp R
        (restrictionMap φ (embeddingUpIntDownIntSub n)) _) _).f k ≫
        (L.regradeBidualXIso n k).hom =
      (K.regradeBidualXIso n k).hom ≫ (linearDualMap (linearDualMap φ)).f (n - k) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ LinearMap.ext fun f ↦ ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [regradeBidualXIso_hom_apply, linearDualMap_f_apply, regradeBidualXIso_hom_apply,
    CochainComplex.linearDualXEquiv_linearHomComplexPrecomp_f_apply]
  congr 1
  refine (CochainComplex.linearDualXEquiv _ (add_neg_cancel k)).injective
    (LinearMap.ext fun x ↦ ?_)
  rw [CochainComplex.linearDualXEquiv_linearHomComplexPrecomp_f_apply,
    restrictionMap_f' _ _ ((embeddingUpIntDownIntSub_f n k).trans (neg_neg (n - k)).symm)]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.apply_symm_apply,
    Iso.inv_hom_id_apply]
  exact (linearDualMap_f_apply φ _ f _).symm

variable {K} in
/-- **Naturality.** The comparison `regradeBidualIso` intertwines the double transposes of a
morphism `φ : K ⟶ L` and of its regrading. -/
@[reassoc]
theorem regradeBidualIso_hom_naturality (φ : K ⟶ L) :
    TauCeti.linearHomComplexPrecomp R (TauCeti.linearHomComplexPrecomp R
        (restrictionMap φ (embeddingUpIntDownIntSub n)) _) _ ≫ (L.regradeBidualIso n).hom =
      (K.regradeBidualIso n).hom ≫
        restrictionMap (linearDualMap (linearDualMap φ)) (embeddingUpIntDownIntSub n) := by
  ext k : 1
  rw [comp_f, comp_f, regradeBidualIso_hom_f, regradeBidualIso_hom_f,
    restrictionMap_f' _ _ (embeddingUpIntDownIntSub_f n k)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, regradeBidualXIso_naturality_assoc]

variable {K} in
/-- **Naturality of the inverse.** The inverse of the comparison `regradeBidualIso` intertwines
the double transposes of a morphism `φ : K ⟶ L` and of its regrading. -/
@[reassoc]
theorem regradeBidualIso_inv_naturality (φ : K ⟶ L) :
    restrictionMap (linearDualMap (linearDualMap φ)) (embeddingUpIntDownIntSub n) ≫
        (L.regradeBidualIso n).inv =
      (K.regradeBidualIso n).inv ≫
        TauCeti.linearHomComplexPrecomp R (TauCeti.linearHomComplexPrecomp R
          (restrictionMap φ (embeddingUpIntDownIntSub n)) _) _ := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← regradeBidualIso_hom_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **The bidual maps of the two gradings differ by `(-1)^n`.** The regrading by `n` of the
chain-compatible bidual map of `K` is `(-1)^n` times the chain-compatible bidual map of the
regrading `C^k = K_(n-k)`, followed by the identification `regradeBidualIso` of the double duals.
An element of `K_(n-k)` has raw degree `n - k` and cochain degree `k`, and the two bidual maps
carry the signs `(-1)^(n-k)` and `(-1)^k`. -/
theorem restrictionMap_bidualHom :
    restrictionMap (bidualHom K) (embeddingUpIntDownIntSub n) =
      n.negOnePow • (CochainComplex.bidualHom (K.restriction (embeddingUpIntDownIntSub n)) ≫
        (K.regradeBidualIso n).hom) := by
  ext k : 1
  -- Compare the two components after reading them in `K∨∨_(n - k)`.
  rw [← cancel_mono ((linearDual (linearDual K)).restrictionXIso (embeddingUpIntDownIntSub n)
    (embeddingUpIntDownIntSub_f n k)).hom, restrictionMap_f' _ _ (embeddingUpIntDownIntSub_f n k),
    units_smul_f_apply, comp_f, regradeBidualIso_hom_f]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Linear.units_smul_comp]
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ LinearMap.ext fun f ↦ ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Units.smul_def, ModuleCat.hom_zsmul,
    LinearMap.smul_apply]
  rw [bidualHom_f_apply, regradeBidualXIso_hom_apply,
    CochainComplex.linearDualXEquiv_bidualHom_f_apply, LinearEquiv.apply_symm_apply,
    LinearMap.comp_apply]
  have hx : (K.XIsoOfEq (neg_neg (n - k)).symm).hom.hom
      ((K.restrictionXIso (embeddingUpIntDownIntSub n) (embeddingUpIntDownIntSub_f n k)).hom.hom
        x) = (K.restrictionXIso (embeddingUpIntDownIntSub n)
          ((embeddingUpIntDownIntSub_f n k).trans (neg_neg (n - k)).symm)).hom.hom x := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
    simp [restrictionXIso, XIsoOfEq]
  rw [hx]
  simp only [Units.smul_def, smul_smul]
  congr 1
  norm_cast
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨-k, by omega⟩

end Regrade

end ChainComplex
