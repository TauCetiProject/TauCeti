/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.KrullSchmidt.Cancellation
public import TauCeti.RingTheory.KrullSchmidt.Existence

/-!
# Cancellation of a Noetherian summand

A Noetherian module `P` cancels from direct sums, `M × P ≃ N × P → M ≃ N`, as soon as each of its
indecomposable direct summands has a local endomorphism ring. The summands with local endomorphism
ring cancel one at a time by Azumaya's argument
`TauCeti.nonempty_linearEquiv_of_prod_linearEquiv_of_isLocalRing_end`; the ascending chain
condition makes the splitting of `P` into indecomposable summands terminate.

The splitting is run as a well-founded induction on the complement of a summand. If a summand `Q`
with complement `K` is neither zero nor indecomposable, it splits as `Q₁ ⊕ Q₂` with both parts
nonzero; then `Q₂` is a summand with complement `K ⊔ Q₁` and `Q₁` one with complement `K ⊔ Q₂`,
and both complements strictly contain `K`. Over a Noetherian module there is no infinite strictly
ascending chain of submodules, so the induction closes.

This is the form in which Krull-Schmidt cancellation is applied to finitely generated modules over
a finite algebra over a complete Noetherian local ring, where the endomorphism rings of
indecomposable modules are local but the modules need not have finite length.

## Main results

* `TauCeti.nonempty_linearEquiv_of_prod_linearEquiv_of_isNoetherian`: a Noetherian module whose
  indecomposable direct summands have local endomorphism rings cancels from a linear equivalence.

## References

* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.10)(i).
-/

public section

namespace TauCeti

universe u v w x y

variable {A : Type u} [Ring A] {P : Type x} [AddCommGroup P] [Module A P]

/-- The induction behind `TauCeti.nonempty_linearEquiv_of_prod_linearEquiv_of_isNoetherian`, run
on the complement `K` of a summand `Q`. The modules being cancelled from live in a universe that
also contains `P`, so that the recursive calls, which enlarge them by summands of `P`, stay
inside it. -/
private theorem nonempty_linearEquiv_of_prod_linearEquiv_of_isCompl [IsNoetherian A P]
    (hP : ∀ Q K : Submodule A P, IsCompl Q K → IsIndecomposableModule A Q →
      IsLocalRing (Module.End A Q))
    (K : Submodule A P) : ∀ Q : Submodule A P, IsCompl Q K →
      ∀ (M N : Type (max y x)) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N],
        Nonempty ((M × Q) ≃ₗ[A] (N × Q)) → Nonempty (M ≃ₗ[A] N) := by
  induction K using WellFoundedGT.induction with
  | ind K ih =>
  intro Q hQK M N _ _ _ _ ⟨e⟩
  rcases eq_or_ne Q ⊥ with rfl | hQ
  · exact ⟨(LinearEquiv.prodUnique.symm.trans e).trans LinearEquiv.prodUnique⟩
  by_cases hind : IsIndecomposableModule A Q
  · have := hP Q K hQK hind
    exact nonempty_linearEquiv_of_prod_linearEquiv_of_isLocalRing_end ⟨e⟩
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hd, hs⟩ := exists_lt_lt_of_not_isIndecomposableModule hQ hind
  -- `Q₂` is complementary to `K ⊔ Q₁`, and `Q₁` to `K ⊔ Q₂`; both strictly contain `K`.
  have hQ₁0 : Q₁ ≠ ⊥ := fun h ↦ hQ₂.ne (by rw [← hs, h, bot_sup_eq])
  have hQ₂0 : Q₂ ≠ ⊥ := fun h ↦ hQ₁.ne (by rw [← hs, h, sup_bot_eq])
  have hcompl₂ : IsCompl Q₂ (K ⊔ Q₁) := by
    refine ⟨?_, codisjoint_iff.mpr ?_⟩
    · rw [sup_comm]
      exact hd.symm.disjoint_sup_right_of_disjoint_sup_left (by rw [sup_comm, hs]; exact hQK.1)
    · rw [← hQK.sup_eq_top, ← hs]
      ac_rfl
  have hcompl₁ : IsCompl Q₁ (K ⊔ Q₂) := by
    refine ⟨?_, codisjoint_iff.mpr ?_⟩
    · rw [sup_comm]
      exact hd.disjoint_sup_right_of_disjoint_sup_left (by rw [hs]; exact hQK.1)
    · rw [← hQK.sup_eq_top, ← hs]
      ac_rfl
  have hlt₁ : K < K ⊔ Q₁ :=
    left_lt_sup.mpr fun h ↦ hQ₁0 ((hQK.1.mono_left hQ₁.le).eq_bot_of_le h)
  have hlt₂ : K < K ⊔ Q₂ :=
    left_lt_sup.mpr fun h ↦ hQ₂0 ((hQK.1.mono_left hQ₂.le).eq_bot_of_le h)
  -- Split `Q ≃ Q₁ × Q₂` by the sum map, then cancel `Q₂` and afterwards `Q₁`.
  have hinj : Function.Injective (Q₁.subtype.coprod Q₂.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range] <;> simp [hd]
  let eQ : (Q₁ × Q₂) ≃ₗ[A] Q := (LinearEquiv.ofInjective _ hinj).trans
    (LinearEquiv.ofEq _ _ (by rw [LinearMap.range_coprod, Submodule.range_subtype,
      Submodule.range_subtype, hs]))
  let split (L : Type (max y x)) [AddCommGroup L] [Module A L] : ((L × Q₁) × Q₂) ≃ₗ[A] (L × Q) :=
    (LinearEquiv.prodAssoc A L Q₁ Q₂).trans ((LinearEquiv.refl A L).prodCongr eQ)
  obtain ⟨e₁⟩ := ih _ hlt₁ Q₂ hcompl₂ (M × Q₁) (N × Q₁) ⟨(split M).trans (e.trans (split N).symm)⟩
  exact ih _ hlt₂ Q₁ hcompl₁ M N ⟨e₁⟩

/-- **Cancellation of a Noetherian summand.** If `P` is a Noetherian module each of whose
indecomposable direct summands has a local endomorphism ring, then a linear equivalence
`M × P ≃ N × P` induces a linear equivalence `M ≃ N`. No hypothesis is placed on `M` and `N`. -/
theorem nonempty_linearEquiv_of_prod_linearEquiv_of_isNoetherian {M : Type v} {N : Type w}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [IsNoetherian A P]
    (hP : ∀ Q K : Submodule A P, IsCompl Q K → IsIndecomposableModule A Q →
      IsLocalRing (Module.End A Q))
    (h : Nonempty ((M × P) ≃ₗ[A] (N × P))) : Nonempty (M ≃ₗ[A] N) := by
  obtain ⟨e⟩ := h
  let eTop : (⊤ : Submodule A P) ≃ₗ[A] P := Submodule.topEquiv
  let eM : (ULift.{max v w x} M × (⊤ : Submodule A P)) ≃ₗ[A] (M × P) :=
    ULift.moduleEquiv.prodCongr eTop
  let eN : (ULift.{max v w x} N × (⊤ : Submodule A P)) ≃ₗ[A] (N × P) :=
    ULift.moduleEquiv.prodCongr eTop
  obtain ⟨f⟩ := nonempty_linearEquiv_of_prod_linearEquiv_of_isCompl.{u, x, max v w} hP ⊥ ⊤
    isCompl_top_bot (ULift.{max v w x} M) (ULift.{max v w x} N) ⟨eM.trans (e.trans eN.symm)⟩
  exact ⟨ULift.moduleEquiv.symm.trans (f.trans ULift.moduleEquiv)⟩

end TauCeti
