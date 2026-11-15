/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Kernel
public import TauCeti.Algebra.Module.AuslanderReiten.Morphism
public import TauCeti.Algebra.Module.AuslanderReiten.TensorCokernel
public import TauCeti.LinearAlgebra.Dual.ModuleMap

/-!
# Auslander–Reiten comparisons under maps of presentations

A commutative square between presenting arrows induces a covariant map between their
Auslander–Reiten translates by dualizing the contravariant transpose map. The embedding
`D Tr(p) → ν(P₁)` commutes with this map and the Nakayama map on the source terms.
Likewise, the transpose tensor–Hom-cokernel equivalence commutes with the square, identifying
the transpose map tensored with a coefficient module with precomposition on the Hom cokernel.
These are the presentation-variable comparisons used in the naturality of AR duality.

Two lifts of the same module map can give different translate maps. Their difference extends
across the canonical embedding into `ν(P₁)`. Over a field, when `P₁` is finite projective,
this is a factorization through an injective module. The same factorization holds for a lift
of a map through a projective module, allowing the translate to act on stable morphisms.

No minimality or finite-dimensionality is required. Finite projectivity is used only for
the tensor–cokernel comparison. The lift factorizations require projectivity of `P₀`,
and the induced translate map needs no projectivity.
The constructions reuse `TauCeti.moduleDualMap`, `AuslanderReitenTranspose.map` and its
lift factorizations, `LinearMap.auslanderReitenTranslateToNakayama`, and
`LinearMap.auslanderReitenTransposeTensorEquivCokernel`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections IV.1–IV.2.
-/

public section

namespace LinearMap

open TauCeti

section Maps

variable {k A P₀ P₁ Q₀ Q₁ : Type*} [CommSemiring k] [Ring A] [Algebra k A]
  [AddCommMonoid P₀] [Module A P₀] [AddCommMonoid P₁] [Module A P₁]
  [AddCommMonoid Q₀] [Module A Q₀] [AddCommMonoid Q₁] [Module A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀}

/-- A presentation square induces a covariant map on `D Tr`, by scalar-dualizing its
contravariant transpose map. -/
def auslanderReitenTranslateMap (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
    (hf : f₀.comp p = q.comp f₁) :
    AuslanderReitenTranslate k p →ₗ[A] AuslanderReitenTranslate k q :=
  moduleDualMap (AuslanderReitenTranspose.map f₀ f₁ hf)
    (LinearEquiv.refl k _) (fun a φ x ↦ by
      simpa only [LinearEquiv.refl_apply] using AuslanderReitenTranslate.smul_apply a φ x)
    (LinearEquiv.refl k _) (fun a φ x ↦ by
      simpa only [LinearEquiv.refl_apply] using AuslanderReitenTranslate.smul_apply a φ x)

/-- The induced translate functional evaluates by the transpose map. -/
@[simp]
theorem auslanderReitenTranslateMap_apply (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
    (hf : f₀.comp p = q.comp f₁) (φ : AuslanderReitenTranslate k p)
    (x : AuslanderReitenTranspose q) :
    auslanderReitenTranslateMap f₀ f₁ hf φ x = φ (AuslanderReitenTranspose.map f₀ f₁ hf x) := by
  rw [auslanderReitenTranslateMap, moduleDualMap_apply]
  rfl

/-- The identity square induces the identity on the translate. -/
@[simp]
theorem auslanderReitenTranslateMap_id :
    auslanderReitenTranslateMap (id : P₀ →ₗ[A] P₀) (id : P₁ →ₗ[A] P₁) (by simp)
      (k := k) (p := p) = id := by
  ext φ x
  simp

/-- A square whose map between source terms vanishes induces zero on translates. -/
@[simp]
theorem auslanderReitenTranslateMap_zero (f₀ : P₀ →ₗ[A] Q₀)
    (hf : f₀.comp p = q.comp (0 : P₁ →ₗ[A] Q₁)) :
    auslanderReitenTranslateMap f₀ (0 : P₁ →ₗ[A] Q₁) hf (k := k) = 0 := by
  ext φ x
  simp

/-- The translate map is additive on presentation squares. -/
@[simp]
theorem auslanderReitenTranslateMap_add (f₀ g₀ : P₀ →ₗ[A] Q₀)
    (f₁ g₁ : P₁ →ₗ[A] Q₁) (hf : f₀.comp p = q.comp f₁) (hg : g₀.comp p = q.comp g₁) :
    auslanderReitenTranslateMap (f₀ + g₀) (f₁ + g₁)
      (by simp [add_comp, comp_add, hf, hg]) (k := k) =
        auslanderReitenTranslateMap f₀ f₁ hf + auslanderReitenTranslateMap g₀ g₁ hg := by
  ext φ x
  rw [auslanderReitenTranslateMap_apply, AuslanderReitenTranspose.map_add f₀ g₀ f₁ g₁ hf hg]
  simp

/-- Dualizing the transpose restores the original order of composition of squares. -/
@[simp]
theorem auslanderReitenTranslateMap_comp_map {R₀ R₁ : Type*}
    [AddCommMonoid R₀] [Module A R₀] [AddCommMonoid R₁] [Module A R₁]
    {r : R₁ →ₗ[A] R₀} (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
    (hf : f₀.comp p = q.comp f₁) (g₀ : Q₀ →ₗ[A] R₀) (g₁ : Q₁ →ₗ[A] R₁)
    (hg : g₀.comp q = r.comp g₁) :
    (auslanderReitenTranslateMap g₀ g₁ hg (k := k)).comp
        (auslanderReitenTranslateMap f₀ f₁ hf) =
      auslanderReitenTranslateMap (g₀.comp f₀) (g₁.comp f₁)
        (by rw [comp_assoc, hf, ← comp_assoc, hg, comp_assoc]) := by
  ext φ x
  simpa only [auslanderReitenTranslateMap_apply, comp_apply] using
    congrArg φ (LinearMap.congr_fun
      (AuslanderReitenTranspose.map_comp_map f₀ f₁ hf g₀ g₁ hg) x)

end Maps

section Nakayama

variable {k A P₀ P₁ Q₀ Q₁ : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀}

/-- The canonical translate embedding is natural in the presenting arrow. Equivalently,
the identification of `D Tr` with the kernel of the Nakayama map respects presentation squares. -/
theorem auslanderReitenTranslateToNakayama_comp_auslanderReitenTranslateMap
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀.comp p = q.comp f₁) :
    (auslanderReitenTranslateToNakayama (k := k) q).comp
        (auslanderReitenTranslateMap f₀ f₁ hf) =
      f₁.nakayamaMap.comp (auslanderReitenTranslateToNakayama p) := by
  ext φ ψ
  simp

/-- Two lifts of the same module map induce translate maps whose difference factors through
the canonical embedding into the source Nakayama module. For a finite projective source
over an algebra over a field, this is a factorization through an injective. -/
theorem exists_auslanderReitenTranslateMap_sub_eq_comp [Module.Projective A P₀]
    {N : Type*} [AddCommGroup N] [Module A N] {ρ : Q₀ →ₗ[A] N}
    (hq : Function.Exact q ρ) (f₀ g₀ : P₀ →ₗ[A] Q₀) (f₁ g₁ : P₁ →ₗ[A] Q₁)
    (hf : f₀.comp p = q.comp f₁) (hg : g₀.comp p = q.comp g₁)
    (hfg : ρ.comp f₀ = ρ.comp g₀) :
    ∃ h : NakayamaModule k A P₁ →ₗ[A] AuslanderReitenTranslate k q,
      auslanderReitenTranslateMap f₀ f₁ hf - auslanderReitenTranslateMap g₀ g₁ hg =
        h.comp (auslanderReitenTranslateToNakayama p) := by
  obtain ⟨h, hh⟩ := AuslanderReitenTranspose.exists_map_sub_eq_mk_comp hq
    f₀ g₀ f₁ g₁ hf hg hfg
  refine ⟨moduleDualMap h (LinearEquiv.refl k _)
    (fun a φ x ↦ by
      simpa only [LinearEquiv.refl_apply] using AuslanderReitenTranslate.smul_apply a φ x)
    (NakayamaModule.equivDual k A P₁) (NakayamaModule.smul_apply k A P₁), ?_⟩
  ext φ x
  rw [comp_apply, moduleDualMap_apply]
  simpa using congrArg φ (LinearMap.congr_fun hh x)

/-- A lift of a module map factoring through a projective induces a translate map factoring
through the source Nakayama module. -/
theorem exists_auslanderReitenTranslateMap_eq_comp_of_factor [Module.Projective A P₀]
    {M N C : Type*} [AddCommMonoid M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommMonoid C] [Module A C] [Module.Projective A C]
    {π : P₀ →ₗ[A] M} {ρ : Q₀ →ₗ[A] N}
    (hp : π.comp p = 0) (hq : Function.Exact q ρ) (hρ : Function.Surjective ρ)
    (i : M →ₗ[A] C) (j : C →ₗ[A] N)
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀.comp p = q.comp f₁)
    (hfactor : ρ.comp f₀ = j.comp (i.comp π)) :
    ∃ h : NakayamaModule k A P₁ →ₗ[A] AuslanderReitenTranslate k q,
      auslanderReitenTranslateMap f₀ f₁ hf =
        h.comp (auslanderReitenTranslateToNakayama p) := by
  obtain ⟨h, hh⟩ := AuslanderReitenTranspose.exists_map_eq_mk_comp_of_factor hp hq hρ
    i j f₀ f₁ hf hfactor
  refine ⟨moduleDualMap h (LinearEquiv.refl k _)
    (fun a φ x ↦ by
      simpa only [LinearEquiv.refl_apply] using AuslanderReitenTranslate.smul_apply a φ x)
    (NakayamaModule.equivDual k A P₁) (NakayamaModule.smul_apply k A P₁), ?_⟩
  ext φ x
  rw [comp_apply, moduleDualMap_apply]
  simpa using congrArg φ (LinearMap.congr_fun hh x)

end Nakayama

section TensorCokernel

variable {k A P₀ P₁ Q₀ Q₁ N : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommMonoid P₀] [Module A P₀] [AddCommMonoid P₁] [Module A P₁]
  [AddCommMonoid Q₀] [Module A Q₀] [AddCommMonoid Q₁] [Module A Q₁]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  [Module.Finite A P₀] [Module.Projective A P₀]
  [Module.Finite A P₁] [Module.Projective A P₁]
  [Module.Finite A Q₀] [Module.Projective A Q₀]
  [Module.Finite A Q₁] [Module.Projective A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀}

/-- The transpose tensor–Hom-cokernel comparison is contravariantly natural in a
presentation square: tensoring the transpose map corresponds to precomposition on the
Hom cokernel. -/
theorem auslanderReitenTransposeTensorEquivCokernel_naturality
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀.comp p = q.comp f₁)
    (z : BalancedTensorProduct k A (AuslanderReitenTranspose q) N) :
    auslanderReitenTransposeTensorEquivCokernel p
        (BalancedTensorProduct.map
          ((AuslanderReitenTranspose.map f₀ f₁ hf).restrictScalars k) id
          (fun a x ↦ by simp only [restrictScalars_apply, map_smul]) (fun _ _ ↦ rfl) z) =
      (range (q.lcomp k N)).mapQ (range (p.lcomp k N)) (f₁.lcomp k N)
        (by
          rintro _ ⟨F, rfl⟩
          refine ⟨F.comp f₀, ?_⟩
          ext x
          exact congrArg F (LinearMap.congr_fun hf x))
        (auslanderReitenTransposeTensorEquivCokernel q z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ht t n =>
    obtain ⟨φ, rfl⟩ := AuslanderReitenTranspose.mk_surjective q t
    rw [BalancedTensorProduct.map_tmul]
    simp only [restrictScalars_apply, AuslanderReitenTranspose.map_mk, id_apply,
      auslanderReitenTransposeTensorEquivCokernel_tmul, Submodule.mapQ_apply]
    congr 1
    ext x
    simp
  | ha z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

end TensorCokernel

end LinearMap
