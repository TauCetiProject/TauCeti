/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The dual of a chain complex of modules

The dual `K∨` of a chain complex `K` of `R`-modules indexed by `ℤ` (`ChainComplex.linearDual`)
has in degree `p` the linear forms on `K_(-p)`, and differential `d f = (-1)^(p + 1) f ∘ d_K` on a
form `f` of degree `p` (`ChainComplex.linearDual_d_apply`). This is the sign convention
`d f = (-1)^(|f| + 1) f ∘ d` of the dual of a cochain complex (`CochainComplex.linearDual`,
`CochainComplex.linearDualXEquiv_d_apply`), in homological degrees. A morphism `φ : K ⟶ L` has the
transpose `ChainComplex.linearDualMap φ : L∨ ⟶ K∨`.

The terms of `K∨` are the dual modules themselves, so that their elements are linear forms. The
comparison with the dual of a cochain complex, through the regrading of chain complexes into
cochain complexes, is in `TauCeti.Algebra.Homology.LinearHomComplex.Regrade`.

**The chain-compatible bidual map.** With this sign convention for the dual differential, the
evaluation `x ↦ (f ↦ f x)` anticommutes with the differentials, and the signed evaluation
`j(x) = (-1)^|x| (f ↦ f x)` is a morphism of complexes `ChainComplex.bidualHom K : K ⟶ K∨∨`, as for
the dual of a cochain complex (`CochainComplex.bidualHom`). Here `|x|` is the homological degree.
It is natural (`ChainComplex.bidualHom_naturality`), satisfies the triangle identity with the
transpose (`ChainComplex.bidualHom_linearDual_comp_linearDualMap_bidualHom`), and is an isomorphism
exactly for complexes of reflexive modules (`ChainComplex.isIso_bidualHom_iff`). Under the
regrading `C^k = K_(n-k)` it becomes `(-1)^n` times the bidual map of the cochain complex `C`
(`ChainComplex.restrictionMap_bidualHom`).

## Main definitions

* `ChainComplex.linearDual`: the dual of a chain complex of modules.
* `ChainComplex.linearDualMap`: the transpose of a morphism of chain complexes.
* `ChainComplex.bidualHom`: the chain-compatible bidual map `K ⟶ K∨∨`.

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
It is an abbreviation whose terms are the dual modules themselves, so its elements are linear
forms (unlike `CochainComplex.linearDual`, whose terms are Hom-complex cochains identified with
forms by `CochainComplex.linearDualXEquiv`). -/
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
@[simp]
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

variable (K) in
/-- Moving a form of `K∨` from degree `p` to degree `q = p` reads it on `K_(-q)` through
`K_(-q) = K_(-p)`. -/
theorem linearDual_XIsoOfEq_hom_apply {p q : ℤ} (h : p = q) (f : (linearDual K).X p)
    (x : K.X (-q)) :
    ((linearDual K).XIsoOfEq h).hom.hom f x =
      f ((K.XIsoOfEq (congrArg Neg.neg h).symm).hom.hom x) := by
  subst h
  simp

variable (K) in
/-- The **chain-compatible bidual map** `K ⟶ K∨∨` of a chain complex, sending `x` of degree `p`
to the form `f ↦ (-1)ᵖ f x` on `K∨_(-p)`, whose elements are the forms on `K_(-(-p)) = K_p`. The
sign makes the evaluation a morphism of complexes. -/
def bidualHom : K ⟶ linearDual (linearDual K) where
  f p := p.negOnePow • ModuleCat.ofHom
    (Module.Dual.eval R (K.X (-(-p))) ∘ₗ (K.XIsoOfEq (neg_neg p).symm).hom.hom)
  comm' p q hpq := by
    obtain rfl : q + 1 = p := hpq
    ext x f
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Units.smul_def, ModuleCat.hom_zsmul,
      LinearMap.smul_apply, ModuleCat.hom_ofHom, Module.Dual.eval_apply, LinearMap.dualMap_apply,
      smul_smul, map_zsmul]
    simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, XIsoOfEq_hom_comp_d,
      d_comp_XIsoOfEq_hom]
    -- The three signs of the two dual differentials and of `j` in degree `q + 1` multiply to the
    -- sign of `j` in degree `q`.
    congr 1
    norm_cast
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨2, by omega⟩

/-- The bidual map sends `x` of degree `p` to the form `f ↦ (-1)ᵖ f x`, with `x` read in
`K_(-(-p))`. -/
@[simp]
theorem bidualHom_f_apply (p : ℤ) (x : K.X p) (f : (linearDual K).X (-p)) :
    ((bidualHom K).f p).hom x f = p.negOnePow • f ((K.XIsoOfEq (neg_neg p).symm).hom.hom x) :=
  (rfl)

/-- **Naturality of the bidual map.** For a morphism `φ : K ⟶ L`, the square formed by `φ`, its
double transpose and the two bidual maps commutes. -/
@[reassoc]
theorem bidualHom_naturality (φ : K ⟶ L) :
    φ ≫ bidualHom L = bidualHom K ≫ linearDualMap (linearDualMap φ) := by
  ext p x f
  simp only [comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [bidualHom_f_apply, linearDualMap_f_apply, bidualHom_f_apply, linearDualMap_f_apply,
    ← LinearMap.comp_apply (φ.f _).hom, ← ModuleCat.hom_comp, ← XIsoOfEq_hom_naturality,
    ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **The triangle identity.** The bidual map of the dual complex, followed by the transpose of
the bidual map of `K`, is the identity of `K∨`. -/
@[reassoc (attr := simp)]
theorem bidualHom_linearDual_comp_linearDualMap_bidualHom :
    bidualHom (linearDual K) ≫ linearDualMap (bidualHom K) = 𝟙 _ := by
  ext p f x
  simp only [comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, id_f, ModuleCat.hom_id,
    LinearMap.id_apply]
  rw [linearDualMap_f_apply, bidualHom_f_apply, bidualHom_f_apply, linearDual_XIsoOfEq_hom_apply,
    smul_smul, ← Int.negOnePow_add, add_neg_cancel, Int.negOnePow_zero, one_smul]
  congr 1
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, XIsoOfEq_hom_comp_XIsoOfEq_hom, XIsoOfEq_rfl,
    Iso.refl_hom, ModuleCat.hom_id, LinearMap.id_apply]

/-- The component of the bidual map in degree `p` is bijective exactly when `K_p` is reflexive. -/
theorem bijective_bidualHom_f_iff (p : ℤ) :
    Function.Bijective ((bidualHom K).f p).hom ↔ Module.IsReflexive R (K.X p) := by
  -- The component is the transport to `K_(-(-p))`, the evaluation map and the sign `(-1)ᵖ`.
  have hf : ⇑((bidualHom K).f p).hom = (fun y ↦ p.negOnePow • y) ∘
      ⇑(Module.Dual.eval R (K.X (-(-p)))) ∘ ⇑(K.XIsoOfEq (neg_neg p).symm).hom.hom :=
    funext fun x ↦ LinearMap.ext fun f ↦ bidualHom_f_apply p x f
  rw [hf, (MulAction.bijective p.negOnePow).of_comp_iff',
    Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso _)]
  have key {q : ℤ} (hq : q = p) :
      Module.IsReflexive R (K.X q) ↔ Module.IsReflexive R (K.X p) := by
    subst hq; rfl
  exact ⟨fun h ↦ (key (neg_neg p)).1 ⟨h⟩, fun h ↦ ((key (neg_neg p)).2 h).bijective_dual_eval'⟩

/-- **The bidual map is an isomorphism exactly for complexes of reflexive modules.** -/
theorem isIso_bidualHom_iff : IsIso (bidualHom K) ↔ ∀ p, Module.IsReflexive R (K.X p) := by
  simp only [← bijective_bidualHom_f_iff]
  refine ⟨fun _ p ↦ (ConcreteCategory.isIso_iff_bijective _).1 inferInstance, fun h ↦ ?_⟩
  have (p : ℤ) : IsIso ((bidualHom K).f p) := (ConcreteCategory.isIso_iff_bijective _).2 (h p)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- For a complex of reflexive modules, such as finitely generated projective ones, the bidual
map is an isomorphism of complexes. -/
instance isIso_bidualHom [∀ p, Module.IsReflexive R (K.X p)] : IsIso (bidualHom K) :=
  (isIso_bidualHom_iff (K := K)).2 inferInstance

end ChainComplex
