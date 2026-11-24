/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.Regrade
public import TauCeti.Algebra.Homology.LinearHomComplex.Bidual

/-!
# Regrading dual complexes

For an integer `n`, a chain complex `K` of modules indexed by `ℤ` (differential of degree `-1`) is
regraded into the cochain complex `C` with `C^k = K_(n-k)` and the same differential
(`ChainComplex.regradeEquivalence`). This is the passage from the raw homological grading of a
Hamiltonian Floer complex `CF_*` to its cohomological grading `C^k = CF_(n-k)`. This file compares
the two ways of forming linear duals: in the raw grading and in the cochain grading.

**The dual of a chain complex.** The dual `K∨` of a chain complex `K` of `R`-modules
(`ChainComplex.linearDual`) has in degree `p` the linear forms on `K_(-p)`, and differential
`d f = (-1)^(p + 1) f ∘ d_K` on a form `f` of degree `p` (`ChainComplex.linearDual_d_apply`). This
is the sign convention `d f = (-1)^(|f| + 1) f ∘ d` of the dual of a cochain complex
(`CochainComplex.linearDual`, `CochainComplex.linearDualXEquiv_d_apply`), in homological
degrees.
A morphism `φ : K ⟶ L` has the transpose `ChainComplex.linearDualMap φ : L∨ ⟶ K∨`.

**Duals and regrading.** The dual `C∨` of the regrading `C` of `K` by `n` has in degree `k` the
linear forms on `C^(-k) = K_(n + k)`; so has the regrading of `K∨` by `-n`, in degree `k` the
term `K∨_(-n - k)`. The two complexes are isomorphic
(`ChainComplex.regradeLinearDualIso`), but not by the identity on forms: the differential of `C∨`
in degree `k` is `(-1)^(k + 1) f ∘ d_K`, that of the regrading of `K∨` is
`(-1)^(-n - k + 1) f ∘ d_K`, and the two differ by `(-1)^n`. The isomorphism is the identity on
forms twisted by the sign `(-1)^(k n)` in degree `k` (`ChainComplex.regradeLinearDualIso_hom_f`),
as for the comparison `ChainComplex.regradeIsoShift` of the regrading with the shift. It is
natural in `K` (`ChainComplex.regradeLinearDualIso_hom_naturality`). For `n = 0` it identifies the
dual of a chain complex with the dual of the cochain complex `K^k = K_(-k)` of Mathlib's
`ChainComplex.cochainComplexEquivalence`, with no sign.

For the Floer complex of a symplectic manifold of dimension `2n`, the external kernel of an
operation counts functionals on tensor products of the generators of the inputs with the duals of
those of the outputs. Its raw and cochain gradings, and the Koszul signs computed in each, are
related by this comparison together with the regrading of tensor products
(`ChainComplex.regradeTensorIso`): the dual of a generator of raw degree `μ` has raw degree `-μ`
and cochain degree `μ - n`.

## Main definitions and results

* `ChainComplex.linearDual`: the dual of a chain complex of modules.
* `ChainComplex.linearDualMap`: the transpose of a morphism of chain complexes.
* `ChainComplex.regradeLinearDualXIso`: the identification, without sign, of the term of degree
  `k` of the dual of the regrading by `n` with the term of degree `-n - k` of the dual.
* `ChainComplex.regradeLinearDualIso`: the isomorphism between the dual of the regrading by `n`
  and the regrading by `-n` of the dual.

## References

* C. A. Weibel, *An introduction to homological algebra*, Section 2.7, on Hom complexes and
  their sign conventions.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex ComplexShape

universe u

namespace ChainComplex

variable {R : Type u} [CommRing R]

/-- The **dual complex** `K∨` of a chain complex `K` of `R`-modules: in degree `p` the linear
forms on `K_(-p)`, with differential `d f = (-1)^(p + 1) f ∘ d_K` on a form `f` of degree `p`.
It is an abbreviation, like `CochainComplex.linearDual`, so that its terms are the dual modules
and their elements are linear forms. -/
abbrev linearDual (K : ChainComplex (ModuleCat.{u} R) ℤ) : ChainComplex (ModuleCat.{u} R) ℤ where
  X p := ModuleCat.of R (Module.Dual R (K.X (-p)))
  d p q := (p + 1).negOnePow • ModuleCat.ofHom (K.d (-q) (-p)).hom.dualMap
  shape p q h := by
    rw [K.shape (-q) (-p) (by simp only [down_Rel] at h ⊢; omega)]
    ext f x
    simp [LinearMap.dualMap_apply]
  d_comp_d' p q r _ _ := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, ← ModuleCat.ofHom_comp,
      LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp, K.d_comp_d]
    ext f x
    simp [LinearMap.dualMap_apply]

variable {K : ChainComplex (ModuleCat.{u} R) ℤ}

/-- **The differential of the dual complex.** On a form `f` of degree `p`, the differential is
`d f = (-1)^(p + 1) f ∘ d_K`. -/
theorem linearDual_d_apply (p q : ℤ) (f : (linearDual K).X p) (x : K.X (-q)) :
    ((linearDual K).d p q).hom f x = (p + 1).negOnePow • f ((K.d (-q) (-p)).hom x) :=
  (rfl)

variable {L M : ChainComplex (ModuleCat.{u} R) ℤ}

/-- The transpose `L∨ ⟶ K∨` of a morphism of chain complexes `φ : K ⟶ L`. -/
def linearDualMap (φ : K ⟶ L) : linearDual L ⟶ linearDual K where
  f p := ModuleCat.ofHom (φ.f (-p)).hom.dualMap
  comm' p q _ := by
    ext f x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.dualMap_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
    rw [← LinearMap.comp_apply (φ.f (-p)).hom, ← ModuleCat.hom_comp, ← φ.comm, ModuleCat.hom_comp,
      LinearMap.comp_apply]

/-- The transpose of `φ` sends a form `f` on `L_(-p)` to `f ∘ φ`. -/
theorem linearDualMap_f_apply (φ : K ⟶ L) (p : ℤ) (f : (linearDual L).X p) (x : K.X (-p)) :
    ((linearDualMap φ).f p).hom f x = f ((φ.f (-p)).hom x) :=
  (rfl)

/-- The transpose of the identity is the identity. -/
@[simp]
theorem linearDualMap_id : linearDualMap (𝟙 K) = 𝟙 _ :=
  (rfl)

/-- The transpose of a composite is the composite of the transposes, in the opposite order. -/
@[simp, reassoc]
theorem linearDualMap_comp (φ : K ⟶ L) (ψ : L ⟶ M) :
    linearDualMap (φ ≫ ψ) = linearDualMap ψ ≫ linearDualMap φ :=
  (rfl)

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

/-- The identification `regradeLinearDualXIso` reads a form on `K_(n + k)` on `K_(-(-n - k))`. -/
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
  rw [← Int.units_inv_eq_self (k * n).negOnePow]
  rfl

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

end Regrade

end ChainComplex
