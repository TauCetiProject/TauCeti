/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.Algebra.Module.Projective.Schanuel
import TauCeti.Algebra.Module.AuslanderReiten.DoubleTranspose.Basic
import TauCeti.LinearAlgebra.Dual.FiniteProjective
import Mathlib.RingTheory.Finiteness.Prod

/-!
# The transpose of an arbitrary projective presentation

The Auslander–Bridger transpose `Tr M` of a module `M` is the cokernel of `Hom_A(-, A)` applied to
the first map `P₁ → P₀` of a projective presentation `P₁ → P₀ → M → 0`
(`TauCeti.AuslanderReitenTranspose`). A *minimal* presentation, when one exists, is unique up to
isomorphism, and so is its transpose. For an arbitrary projective presentation — a presentation by
free modules of some finite rank, say, which is what a finiteness hypothesis on a module supplies —
the transpose depends on the chosen presentation, but only through summands of the form
`Hom_A(P, A)` with `P` projective. This file proves that independence.

The transpose is additive in the presenting arrow: the transpose of `u ⊕ w` is the sum of the
transposes (`TauCeti.AuslanderReitenTranspose.prodMapEquiv`), and enlarging the source of `u` by a
summand `C` on which the arrow vanishes adds `Hom_A(C, A)`
(`TauCeti.AuslanderReitenTranspose.compFstEquiv`). Since two projective presentations of the same
module become isomorphic arrows after enlarging each by the identity of the other's middle term
and a zero map out of the remaining projectives
(`TauCeti.exists_linearEquiv_comp_prodMap_comp_fst_eq`), their transposes agree after adding
the corresponding duals.

When the presentations are by finitely generated projectives, the duals `Hom_A(P, A)` are finitely
generated projective `Aᵐᵒᵖ`-modules, so the transpose of a finitely presented module is well defined
up to adding finitely generated projectives. Combined with the other half of the Auslander–Bridger
duality, that transposing a dual presentation returns the presented module
(`TauCeti.doubleTransposePresentationEquiv`), this shows that the transpose determines a finitely
presented module up to finitely generated projective summands: modules with isomorphic transposes
become isomorphic after adding finitely generated projectives. This is how Neukirch–Schmidt–Wingberg
compare modules of projective dimension one over the group ring `ℤ_p[G]` of a finite group through
their `Ext¹(-, ℤ_p[G])`, which is the transpose of such a module.

## Main definitions

* `TauCeti.AuslanderReitenTranspose.prodMapEquiv`: the transpose of a direct sum of arrows is the
  direct sum of the transposes.
* `TauCeti.AuslanderReitenTranspose.compFstEquiv`: the transpose of `u ∘ fst : A₁ × C → E` is the
  transpose of `u` plus `Hom_A(C, A)`.

## Main results

* `TauCeti.AuslanderReitenTranspose.nonempty_linearEquiv_prod_dual`: for two projective
  presentations `P₁ → P₀ → M` and `Q₁ → Q₀ → M` of the same module,
  `Tr(P₁ → P₀) ⊕ Hom_A(P₀ × Q₁, A) ≃ Tr(Q₁ → Q₀) ⊕ Hom_A(P₁ × Q₀, A)`.
* `TauCeti.AuslanderReitenTranspose.nonempty_linearEquiv_prod_of_linearEquiv`: for finite projective
  presentations `P₁ → P₀ → M` and `Q₁ → Q₀ → N` with isomorphic transposes,
  `M ⊕ P₁ ⊕ Q₀ ≃ N ⊕ P₀ ⊕ Q₁`.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren 323,
  Springer (2008), (5.4.11).
-/

public section

namespace TauCeti

namespace AuslanderReitenTranspose

open LinearMap

variable {A : Type*} [Ring A]

section Presentation

variable {M P₀ P₁ Q₀ Q₁ : Type*} [AddCommMonoid M] [Module A M]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  [Module.Projective A P₀] [Module.Projective A P₁]
  [Module.Projective A Q₀] [Module.Projective A Q₁]

/-- **The transpose is independent of the projective presentation up to projective duals.** For
two projective presentations `P₁ → P₀ → M → 0` and `Q₁ → Q₀ → M → 0` of the same module, with first
maps `f` and `g`, the transposes satisfy
`Tr f ⊕ Hom_A(P₀ × Q₁, A) ≃ Tr g ⊕ Hom_A(P₁ × Q₀, A)` as `Aᵐᵒᵖ`-modules.

No finiteness is assumed, and the presented module is arbitrary. -/
theorem nonempty_linearEquiv_prod_dual {f : P₁ →ₗ[A] P₀} {π : P₀ →ₗ[A] M}
    {g : Q₁ →ₗ[A] Q₀} {ρ : Q₀ →ₗ[A] M} (hf : Function.Exact f π) (hπ : Function.Surjective π)
    (hg : Function.Exact g ρ) (hρ : Function.Surjective ρ) :
    Nonempty ((AuslanderReitenTranspose f × Module.Dual A (P₀ × Q₁)) ≃ₗ[Aᵐᵒᵖ]
      (AuslanderReitenTranspose g × Module.Dual A (P₁ × Q₀))) := by
  obtain ⟨e₀, e₁, he⟩ := exists_linearEquiv_comp_prodMap_comp_fst_eq hf hπ hg hρ
  -- The transposes of the identity arrows vanish.
  have hTrQ₀ : Subsingleton (AuslanderReitenTranspose (LinearMap.id : Q₀ →ₗ[A] Q₀)) :=
    subsingleton_of_comp_eq_id (LinearMap.id : Q₀ →ₗ[A] Q₀) (LinearMap.id_comp _)
  have hTrP₀ : Subsingleton (AuslanderReitenTranspose (LinearMap.id : P₀ →ₗ[A] P₀)) :=
    subsingleton_of_comp_eq_id (LinearMap.id : P₀ →ₗ[A] P₀) (LinearMap.id_comp _)
  let hUniqueTrQ₀ : Unique (AuslanderReitenTranspose (LinearMap.id : Q₀ →ₗ[A] Q₀)) :=
    uniqueOfSubsingleton 0
  let hUniqueTrP₀ : Unique (AuslanderReitenTranspose (LinearMap.id : P₀ →ₗ[A] P₀)) :=
    uniqueOfSubsingleton 0
  -- The enlarged first presentation `(f ⊕ id) ∘ fst` has transpose `Tr f ⊕ Hom(P₀ × Q₁, A)`.
  let eP : AuslanderReitenTranspose (f.prodMap (LinearMap.id : Q₀ →ₗ[A] Q₀) ∘ₗ
      fst A (P₁ × Q₀) (P₀ × Q₁)) ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose f × Module.Dual A (P₀ × Q₁) :=
    (compFstEquiv _ _).trans
      (((prodMapEquiv f _).trans LinearEquiv.prodUnique).prodCongr (.refl _ _))
  -- The enlarged second presentation `(id ⊕ g) ∘ snd`, after swapping its source, has transpose
  -- `Tr g ⊕ Hom(P₁ × Q₀, A)`.
  let eQ : AuslanderReitenTranspose ((LinearMap.id : P₀ →ₗ[A] P₀).prodMap g ∘ₗ
      snd A (P₁ × Q₀) (P₀ × Q₁)) ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose g × Module.Dual A (P₁ × Q₀) :=
    (linearEquiv (q₁ := (LinearMap.id : P₀ →ₗ[A] P₀).prodMap g ∘ₗ fst A (P₀ × Q₁) (P₁ × Q₀))
      (.refl A _) (LinearEquiv.prodComm A _ _) (by ext <;> simp)).trans <|
      (compFstEquiv _ _).trans
        (((prodMapEquiv _ g).trans LinearEquiv.uniqueProd).prodCongr (.refl _ _))
  exact ⟨eP.symm.trans ((linearEquiv e₀ e₁ he).trans eQ)⟩

end Presentation

section Recovery

variable {M N P₀ P₁ Q₀ Q₁ : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  [Module.Finite A P₀] [Module.Projective A P₀] [Module.Finite A P₁] [Module.Projective A P₁]

/-- Transposing the dual of a finite projective presentation of `M`, and taking the opposite double
dual of finite projectives `C₁` and `C₂`, recovers `M ⊕ C₁ ⊕ C₂`, semilinearly along
`Aᵐᵒᵖᵐᵒᵖ ≃+* A`. -/
private noncomputable def doubleTransposeProdEquiv {C₁ C₂ : Type*}
    [AddCommGroup C₁] [Module A C₁] [Module.Finite A C₁] [Module.Projective A C₁]
    [AddCommGroup C₂] [Module A C₂] [Module.Finite A C₂] [Module.Projective A C₂]
    {f : P₁ →ₗ[A] P₀} {π : P₀ →ₗ[A] M} (hf : Function.Exact f π) (hπ : Function.Surjective π) :
    (AuslanderReitenTranspose (f.lcomp Aᵐᵒᵖ A) ×
      Module.Dual Aᵐᵒᵖ (Module.Dual A C₁ × Module.Dual A C₂))
        ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.opOp A).symm] M × (C₁ × C₂) :=
  let eM := doubleTransposePresentationEquiv A f π hf hπ
  let eC := (LinearEquiv.congrLeft Aᵐᵒᵖ Aᵐᵒᵖᵐᵒᵖ (LinearMap.coprodEquiv Aᵐᵒᵖ)).trans
    ((opDualCodomainEquiv A _).symm.trans (opDualEvalEquiv A (C₁ × C₂)).symm)
  -- Mathlib's `LinearEquiv.prodCongr` is stated only for linear equivalences, so the product of
  -- these semilinear ones is assembled from `AddEquiv.prodCongr` in the same way.
  { eM.toAddEquiv.prodCongr eC.toAddEquiv with
    map_smul' := fun c x ↦ Prod.ext (eM.map_smulₛₗ c x.1) (eC.map_smulₛₗ c x.2) }

variable [Module.Finite A Q₀] [Module.Projective A Q₀] [Module.Finite A Q₁] [Module.Projective A Q₁]

/-- **The transpose determines a module up to projective summands.** For finite projective
presentations `P₁ → P₀ → M → 0` and `Q₁ → Q₀ → N → 0`, with first maps `f` and `g`, an isomorphism
of transposes `Tr f ≃ Tr g` gives `M ⊕ P₁ ⊕ Q₀ ≃ N ⊕ P₀ ⊕ Q₁` as `A`-modules.

The ring `A` may be noncommutative, and no minimality of the presentations is needed. -/
theorem nonempty_linearEquiv_prod_of_linearEquiv {f : P₁ →ₗ[A] P₀} {π : P₀ →ₗ[A] M}
    {g : Q₁ →ₗ[A] Q₀} {ρ : Q₀ →ₗ[A] N} (hf : Function.Exact f π) (hπ : Function.Surjective π)
    (hg : Function.Exact g ρ) (hρ : Function.Surjective ρ)
    (e : AuslanderReitenTranspose f ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose g) :
    Nonempty ((M × (P₁ × Q₀)) ≃ₗ[A] (N × (P₀ × Q₁))) := by
  -- The dual arrows present `Tr f` twice over `Aᵐᵒᵖ`, the second time through `e`.
  have hf' : Function.Exact (f.lcomp Aᵐᵒᵖ A) (mk f) := by
    rw [LinearMap.exact_iff, ker_mk]
  have hg' : Function.Exact (g.lcomp Aᵐᵒᵖ A) (e.symm.toLinearMap ∘ₗ mk g) := by
    rw [LinearMap.exact_iff, LinearEquiv.ker_comp, ker_mk]
  obtain ⟨e'⟩ := nonempty_linearEquiv_prod_dual hf' (mk_surjective f) hg'
    (e.symm.surjective.comp (mk_surjective g))
  -- Transposing the two dual presentations returns `M` and `N`.
  exact ⟨(doubleTransposeProdEquiv hf hπ).symm.trans (e'.trans (doubleTransposeProdEquiv hg hρ))⟩

end Recovery

end AuslanderReitenTranspose

end TauCeti
