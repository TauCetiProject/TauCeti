/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic

/-!
# The chain-compatible bidual map of a complex of modules

Let `K` be a cochain complex of modules over a commutative ring `R`. Its dual complex
`K∨ = Hom(K, R)` (`CochainComplex.linearDual`) is Mathlib's Hom complex into `R` placed in degree
`0`. Its term of degree `n` is the dual of `K⁻ⁿ` (`CochainComplex.linearDualXEquiv`), and its
differential is `d f = (-1)^(n + 1) f ∘ d_K` on a form `f` of degree `n`
(`CochainComplex.linearDualXEquiv_d_apply`).

Evaluation `x ↦ (f ↦ f x)` sends `Kᵖ` to the linear forms on `(K∨)⁻ᵖ`, that is, to the term of
degree `p` of the double dual `K∨∨` (`CochainComplex.bidualEval`). With this sign convention for
the dual differential, evaluation is **not** a morphism of complexes: it anticommutes with the
differentials (`CochainComplex.bidualEval_comp_d`). The signed evaluation `j(x) = (-1)^|x| f x`
commutes with them. It is the **chain-compatible bidual map** `CochainComplex.bidualHom K`, a
morphism of complexes `K ⟶ K∨∨`.

Orientation conventions for moduli spaces of Floer trajectories and pairs of pants record a count
as a functional on an external kernel such as `A ⊗ B∨`, for an operation from `A` to `B`, and read
it as an operator through `(A ⊗ B∨)∨ ≅ B∨∨ ⊗ A∨` and the inverse of `j` on `B∨∨`. The sign of `j`
is what makes that reading compatible with the differentials. This file provides `j` and its
basic properties; the tensor identifications are not treated here.

* `CochainComplex.bidualHom_naturality`: the bidual map is natural in morphisms of complexes.
* `CochainComplex.bidualHom_linearDual_comp_linearHomComplexPrecomp_bidualHom`: the triangle
  identity: the bidual map of `K∨` followed by the transpose of the bidual map of `K` is the
  identity of `K∨`.
* `CochainComplex.isIso_bidualHom_iff`: the bidual map is an isomorphism of complexes exactly when
  every term of `K` is a reflexive module, for instance a finitely generated projective one
  (`CochainComplex.isIso_bidualHom`), such as a free module of rank one.

The dual complex, its differential and the identification of its terms with cochains are those of
Mathlib's `CochainComplex.HomComplex` and `CochainComplex.HomComplex.Cochain.toSingleLinearEquiv`.
-/

public section

noncomputable section

open CategoryTheory CochainComplex HomComplex

universe u

namespace CochainComplex

variable (R : Type u) [CommRing R]

/-- The **dual complex** `K∨ = Hom(K, R)` of a cochain complex of `R`-modules: Mathlib's Hom
complex from `K` to `R` placed in degree `0`. Its term of degree `n` consists of the linear forms
on `K⁻ⁿ` (`CochainComplex.linearDualXEquiv`). -/
abbrev linearDual (K : CochainComplex (ModuleCat.{u} R) ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))

variable {R} (K L : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The term of degree `n` of the dual complex, the module of cochains of degree `n` from `K` to
`R`, is the dual of the term of degree `p = -n` of `K`. -/
def linearDualXEquiv {p n : ℤ} (h : p + n = 0) :
    Cochain K ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) n ≃ₗ[R]
      Module.Dual R (K.X p) :=
  (Cochain.toSingleLinearEquiv h).trans ModuleCat.homLinearEquiv

variable {K}

/-- The form on `Kᵖ` of a cochain of degree `n = -p` of the dual complex. -/
theorem linearDualXEquiv_apply {p n : ℤ} (h : p + n = 0)
    (f : Cochain K ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) n) (x : K.X p) :
    linearDualXEquiv K h f x = (Cochain.toSingleEquiv h f).hom x :=
  (rfl)

/-- The cochain of degree `n = -p` of the dual complex of a form on `Kᵖ`. -/
@[simp]
theorem linearDualXEquiv_symm_apply {p n : ℤ} (h : p + n = 0) (f : Module.Dual R (K.X p)) :
    (linearDualXEquiv K h).symm f = Cochain.toSingleMk (ModuleCat.ofHom f) h :=
  (rfl)

/-- The form on `Kᵖ` of the cochain of the dual complex given by a morphism `g : Kᵖ ⟶ R`. -/
@[simp]
theorem linearDualXEquiv_toSingleMk {p n : ℤ} (h : p + n = 0) (g : K.X p ⟶ ModuleCat.of R R) :
    linearDualXEquiv K h (Cochain.toSingleMk g h) = g.hom :=
  (linearDualXEquiv K h).apply_symm_apply g.hom

/-- **The differential of the dual complex.** On a form `f` of degree `n`, the differential is
`d f = (-1)^(n + 1) f ∘ d_K`. -/
theorem linearDualXEquiv_d_apply {p p' n n' : ℤ} (h : p + n = 0) (h' : p' + n' = 0)
    (f : (linearDual R K).X n) (x : K.X p') :
    linearDualXEquiv K h' (((linearDual R K).d n n').hom f) x =
      n'.negOnePow • linearDualXEquiv K h f ((K.d p' p).hom x) := by
  obtain ⟨f, rfl⟩ := (linearDualXEquiv K h).symm.surjective f
  rw [linearDualXEquiv_symm_apply, linearHomComplex_d_hom_apply,
    Cochain.δ_toSingleMk (h' := h')]
  simp

/-- Precomposition by a morphism `φ : K ⟶ L` acts on the dual complexes by the transpose of `φ`. -/
theorem linearDualXEquiv_linearHomComplexPrecomp_f_apply (φ : K ⟶ L) {p n : ℤ} (h : p + n = 0)
    (f : (linearDual R L).X n) (x : K.X p) :
    linearDualXEquiv K h (((TauCeti.linearHomComplexPrecomp R φ _).f n).hom f) x =
      linearDualXEquiv L h f ((φ.f p).hom x) := by
  obtain ⟨f, rfl⟩ := (linearDualXEquiv L h).symm.surjective f
  simp [← Cochain.toSingleMk_precomp]

variable (K)

/-- The **unsigned evaluation** `Kᵖ ⟶ (K∨∨)ᵖ`, sending `x` to the form `f ↦ f x` on `(K∨)⁻ᵖ`.
It anticommutes with the differentials (`CochainComplex.bidualEval_comp_d`); the
chain-compatible bidual map `CochainComplex.bidualHom` is `(-1)ᵖ` times it. -/
def bidualEval (p : ℤ) : K.X p ⟶ (linearDual R (linearDual R K)).X p :=
  ModuleCat.ofHom <| (linearDualXEquiv (linearDual R K) (neg_add_cancel p)).symm.toLinearMap ∘ₗ
    (linearDualXEquiv K (add_neg_cancel p)).dualMap.toLinearMap ∘ₗ Module.Dual.eval R (K.X p)

variable {K}

/-- The unsigned evaluation of `x` takes the value `f x` on a form `f`. -/
theorem linearDualXEquiv_bidualEval_apply {p q : ℤ} (h' : q + p = 0) (x : K.X p)
    (f : (linearDual R K).X q) :
    linearDualXEquiv (linearDual R K) h' ((bidualEval K p).hom x) f =
      linearDualXEquiv K (by omega) f x := by
  obtain rfl : q = -p := by omega
  simp [bidualEval]

/-- A morphism into a term of the dual complex is determined by the values of the forms it
produces. -/
theorem linearDual_X_hom_ext {p n : ℤ} (h : p + n = 0) {M : ModuleCat.{u} R}
    {g g' : M ⟶ (linearDual R K).X n}
    (hg : ∀ m x, linearDualXEquiv K h (g.hom m) x = linearDualXEquiv K h (g'.hom m) x) :
    g = g' :=
  ModuleCat.hom_ext <| LinearMap.ext fun m ↦
    (linearDualXEquiv K h).injective (LinearMap.ext (hg m))

variable (K) in
/-- **The unsigned evaluation anticommutes with the differentials.** With the dual differential
`d f = (-1)^(|f| + 1) f ∘ d`, the evaluation `x ↦ (f ↦ f x)` satisfies `d ∘ eval = -(eval ∘ d)`. -/
theorem bidualEval_comp_d {p q : ℤ} (hpq : p + 1 = q) :
    bidualEval K p ≫ (linearDual R (linearDual R K)).d p q = -(K.d p q ≫ bidualEval K q) := by
  -- The two signs of the dual differentials multiply to `(-1)^(p + 1) (-1)^p = -1`.
  have hsign : q.negOnePow * p.negOnePow = -1 := by
    rw [← hpq, Int.negOnePow_succ, neg_mul, Int.units_mul_self]
  refine linearDual_X_hom_ext (neg_add_cancel q) fun x f ↦ ?_
  simp only [ModuleCat.hom_comp, ModuleCat.hom_neg, LinearMap.comp_apply, LinearMap.neg_apply,
    map_neg, linearDualXEquiv_d_apply (neg_add_cancel p), linearDualXEquiv_bidualEval_apply,
    linearDualXEquiv_d_apply (add_neg_cancel q) (add_neg_cancel p), smul_smul,
    Int.negOnePow_neg, hsign, Units.neg_smul, one_smul]

variable (K) in
/-- The **chain-compatible bidual map** `K ⟶ K∨∨`, sending `x` of degree `p` to the form
`f ↦ (-1)ᵖ f x` on `(K∨)⁻ᵖ`. The sign makes the evaluation of `CochainComplex.bidualEval` a
morphism of complexes. -/
def bidualHom : K ⟶ linearDual R (linearDual R K) where
  f p := p.negOnePow • bidualEval K p
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    rw [Linear.units_smul_comp, bidualEval_comp_d K rfl, Linear.comp_units_smul, smul_neg,
      ← Units.neg_smul, ← Int.negOnePow_succ]

/-- The bidual map is `(-1)ᵖ` times the evaluation in degree `p`. -/
theorem bidualHom_f (p : ℤ) : (bidualHom K).f p = p.negOnePow • bidualEval K p :=
  (rfl)

/-- The bidual map sends `x` of degree `p` to the form `f ↦ (-1)ᵖ f x`. -/
theorem linearDualXEquiv_bidualHom_f_apply {p q : ℤ} (h' : q + p = 0) (x : K.X p)
    (f : (linearDual R K).X q) :
    linearDualXEquiv (linearDual R K) h' (((bidualHom K).f p).hom x) f =
      p.negOnePow • linearDualXEquiv K (by omega) f x := by
  simp only [bidualHom_f, ModuleCat.hom_smul, LinearMap.smul_apply, map_zsmul_unit,
    linearDualXEquiv_bidualEval_apply]

/-- **Naturality of the bidual map.** For a morphism `φ : K ⟶ L`, the square formed by `φ`, its
double transpose and the two bidual maps commutes. -/
@[reassoc]
theorem bidualHom_naturality (φ : K ⟶ L) :
    φ ≫ bidualHom L = bidualHom K ≫ TauCeti.linearHomComplexPrecomp R
      (TauCeti.linearHomComplexPrecomp R φ _) _ := by
  ext p : 1
  refine linearDual_X_hom_ext (neg_add_cancel p) fun x f ↦ ?_
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    linearDualXEquiv_linearHomComplexPrecomp_f_apply, linearDualXEquiv_bidualHom_f_apply]

/-- **The triangle identity.** The bidual map of the dual complex, followed by the transpose of
the bidual map of `K`, is the identity of `K∨`. -/
@[reassoc (attr := simp)]
theorem bidualHom_linearDual_comp_linearHomComplexPrecomp_bidualHom :
    bidualHom (linearDual R K) ≫ TauCeti.linearHomComplexPrecomp R (bidualHom K) _ = 𝟙 _ := by
  ext n : 1
  refine linearDual_X_hom_ext (neg_add_cancel n) fun f x ↦ ?_
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply,
    linearDualXEquiv_linearHomComplexPrecomp_f_apply, linearDualXEquiv_bidualHom_f_apply,
    smul_smul, ← Int.negOnePow_add, add_neg_cancel, Int.negOnePow_zero, one_smul]

/-- The component of the bidual map in degree `p` is bijective exactly when `Kᵖ` is reflexive. -/
theorem bijective_bidualHom_f_iff (p : ℤ) :
    Function.Bijective ((bidualHom K).f p).hom ↔ Module.IsReflexive R (K.X p) := by
  -- The component is the evaluation map, followed by the sign `(-1)ᵖ` and two identifications.
  let E := (linearDualXEquiv K (add_neg_cancel p)).dualMap.trans
    (linearDualXEquiv (linearDual R K) (neg_add_cancel p)).symm
  have hf : ⇑((bidualHom K).f p).hom =
      ⇑E ∘ (fun y ↦ p.negOnePow • y) ∘ ⇑(Module.Dual.eval R (K.X p)) := by
    funext x
    simp [E, bidualHom_f, bidualEval]
  rw [hf, E.bijective.of_comp_iff', (MulAction.bijective p.negOnePow).of_comp_iff']
  exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.bijective_dual_eval'⟩

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

/-- For a complex of reflexive modules, the inverse of the bidual map sends a form `y` of degree
`p` on `K∨` to the element `x` of `Kᵖ` with `f x = (-1)ᵖ y f` for every form `f` on `Kᵖ`. -/
theorem linearDualXEquiv_inv_bidualHom_f_apply [∀ p, Module.IsReflexive R (K.X p)] {p q : ℤ}
    (h : p + q = 0) (y : (linearDual R (linearDual R K)).X p) (f : (linearDual R K).X q) :
    linearDualXEquiv K h f (((inv (bidualHom K)).f p).hom y) =
      p.negOnePow • linearDualXEquiv (linearDual R K) (by omega) y f := by
  conv_rhs => rw [← Iso.inv_hom_id_apply (HomologicalComplex.Hom.isoApp (asIso (bidualHom K)) p) y]
  rw [HomologicalComplex.Hom.isoApp_hom, HomologicalComplex.Hom.isoApp_inv, asIso_hom, asIso_inv,
    linearDualXEquiv_bidualHom_f_apply, smul_smul, Int.units_mul_self, one_smul]

end CochainComplex
