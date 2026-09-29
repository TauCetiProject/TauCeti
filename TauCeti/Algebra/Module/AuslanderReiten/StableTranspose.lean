/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.Algebra.Module.Projective.Schanuel

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
up to adding finitely generated projectives. This is the first half of the Auslander–Bridger
duality, the other being that transposing twice returns the module up to projective summands; it
is how Neukirch–Schmidt–Wingberg compare modules of projective dimension one over the group ring
`ℤ_p[G]` of a finite group through their `Ext¹(-, ℤ_p[G])`, which is the transpose of such a
module.

## Main definitions

* `TauCeti.AuslanderReitenTranspose.prodMapEquiv`: the transpose of a direct sum of arrows is the
  direct sum of the transposes.
* `TauCeti.AuslanderReitenTranspose.compFstEquiv`: the transpose of `u ∘ fst : A₁ × C → E` is the
  transpose of `u` plus `Hom_A(C, A)`.

## Main results

* `TauCeti.AuslanderReitenTranspose.nonempty_linearEquiv_prod_dual`: for two projective
  presentations `P₁ → P₀ → M` and `Q₁ → Q₀ → M` of the same module,
  `Tr(P₁ → P₀) ⊕ Hom_A(P₀ × Q₁, A) ≃ Tr(Q₁ → Q₀) ⊕ Hom_A(P₁ × Q₀, A)`.

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

section Additivity

variable {A₁ A₂ E₁ E₂ : Type*} [AddCommMonoid A₁] [Module A A₁] [AddCommMonoid A₂] [Module A A₂]
  [AddCommMonoid E₁] [Module A E₁] [AddCommMonoid E₂] [Module A E₂]
  (u : A₁ →ₗ[A] E₁) (w : A₂ →ₗ[A] E₂)

/-- **The transpose is additive.** The transpose of the direct sum `u ⊕ w` of two arrows is the
direct sum of their transposes. On representatives it restricts a functional on `A₁ × A₂` to the
two summands. -/
def prodMapEquiv :
    AuslanderReitenTranspose (u.prodMap w) ≃ₗ[Aᵐᵒᵖ]
      AuslanderReitenTranspose u × AuslanderReitenTranspose w :=
  LinearEquiv.ofLinearMap
    (lift (u.prodMap w)
      ((mk u ∘ₗ (inl A A₁ A₂).lcomp Aᵐᵒᵖ A).prod (mk w ∘ₗ (inr A A₁ A₂).lcomp Aᵐᵒᵖ A))
      fun φ => by
        refine Prod.ext ((mk_eq_zero_iff _ _).mpr ⟨φ ∘ₗ inl A E₁ E₂, ?_⟩)
          ((mk_eq_zero_iff _ _).mpr ⟨φ ∘ₗ inr A E₁ E₂, ?_⟩) <;> ext <;> simp)
    ((lift u (mk (u.prodMap w) ∘ₗ (fst A A₁ A₂).lcomp Aᵐᵒᵖ A) fun φ =>
        (mk_eq_zero_iff _ _).mpr ⟨φ ∘ₗ fst A E₁ E₂, by ext <;> simp⟩).coprod
      (lift w (mk (u.prodMap w) ∘ₗ (snd A A₁ A₂).lcomp Aᵐᵒᵖ A) fun φ =>
        (mk_eq_zero_iff _ _).mpr ⟨φ ∘ₗ snd A E₁ E₂, by ext <;> simp⟩))
    (by
      apply prod_ext <;> ext φ <;> simp [lcomp_apply', comp_assoc])
    (by
      ext φ
      simp only [comp_apply, lift_mk, coprod_apply, prod_apply, Function.prod, lcomp_apply',
        id_apply]
      rw [← map_add]
      congr 1
      ext <;> simp [← Prod.zero_eq_mk])

/-- The equivalence `prodMapEquiv` restricts a representative to the two summands. -/
@[simp]
theorem prodMapEquiv_mk (φ : Module.Dual A (A₁ × A₂)) :
    prodMapEquiv u w (mk (u.prodMap w) φ) =
      (mk u (φ ∘ₗ inl A A₁ A₂), mk w (φ ∘ₗ inr A A₁ A₂)) := by
  simp [prodMapEquiv, lcomp_apply']

variable (C : Type*) [AddCommMonoid C] [Module A C]

/-- **A zero summand contributes its dual.** Enlarging the source of `u : A₁ → E₁` by a summand
`C` on which the arrow vanishes adds `Hom_A(C, A)` to the transpose. On representatives it
restricts a functional on `A₁ × C` to the two summands. -/
def compFstEquiv :
    AuslanderReitenTranspose (u ∘ₗ fst A A₁ C) ≃ₗ[Aᵐᵒᵖ]
      AuslanderReitenTranspose u × Module.Dual A C :=
  LinearEquiv.ofLinearMap
    (lift (u ∘ₗ fst A A₁ C)
      ((mk u ∘ₗ (inl A A₁ C).lcomp Aᵐᵒᵖ A).prod ((inr A A₁ C).lcomp Aᵐᵒᵖ A))
      fun φ => by
        refine Prod.ext ((mk_eq_zero_iff _ _).mpr ⟨φ, ?_⟩) ?_ <;> ext <;> simp)
    ((lift u (mk (u ∘ₗ fst A A₁ C) ∘ₗ (fst A A₁ C).lcomp Aᵐᵒᵖ A) fun φ =>
        (mk_eq_zero_iff _ _).mpr ⟨φ, by ext <;> simp⟩).coprod
      (mk (u ∘ₗ fst A A₁ C) ∘ₗ (snd A A₁ C).lcomp Aᵐᵒᵖ A))
    (by
      apply prod_ext <;> ext φ <;> simp [lcomp_apply', comp_assoc])
    (by
      ext φ
      simp only [comp_apply, lift_mk, coprod_apply, prod_apply, Function.prod, lcomp_apply',
        id_apply]
      rw [← map_add]
      congr 1
      ext <;> simp [← Prod.zero_eq_mk])

/-- The equivalence `compFstEquiv` restricts a representative to the two summands. -/
@[simp]
theorem compFstEquiv_mk (φ : Module.Dual A (A₁ × C)) :
    compFstEquiv u C (mk (u ∘ₗ fst A A₁ C) φ) = (mk u (φ ∘ₗ inl A A₁ C), φ ∘ₗ inr A A₁ C) := by
  simp [compFstEquiv, lcomp_apply']

end Additivity

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
  have := subsingleton_of_comp_eq_id (LinearMap.id : Q₀ →ₗ[A] Q₀) (LinearMap.id_comp _)
  have := subsingleton_of_comp_eq_id (LinearMap.id : P₀ →ₗ[A] P₀) (LinearMap.id_comp _)
  let := uniqueOfSubsingleton (α := AuslanderReitenTranspose (LinearMap.id : Q₀ →ₗ[A] Q₀)) 0
  let := uniqueOfSubsingleton (α := AuslanderReitenTranspose (LinearMap.id : P₀ →ₗ[A] P₀)) 0
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

end AuslanderReitenTranspose

end TauCeti
