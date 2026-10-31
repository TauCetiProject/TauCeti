/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Tor
public import TauCeti.Algebra.Category.ModuleCat.Quotient
public import TauCeti.RingTheory.Ideal.Radical
public import TauCeti.RingTheory.Perfect.TensorProduct

/-!
# Tor independence of radical quotients of perfect rings

Let `A` be a perfect ring of prime characteristic `p`, let `I` be a radical ideal of `A` and let
`C` be a perfect `A`-algebra. We show that `Tor_i^A(A ⧸ I, C) = 0` for every `i > 0`, with `Tor`
Mathlib's `CategoryTheory.Tor` in `ModuleCat A`. Thus the derived tensor product of `A ⧸ I` and `C`
over `A` is concentrated in degree zero, where it is `(A ⧸ I) ⊗[A] C ≃ C ⧸ I C`. This is the case
`B = A ⧸ I` of the Tor independence of perfect rings, which asserts `Tor_i^A(B, C) = 0` for all
`i > 0` and all maps `B ← A → C` of perfect rings; the general case reduces to this one by
presenting `B` as a quotient of a perfect polynomial algebra over `A`, which is flat over `A`.

As in the proof of Bhatt and Scholze, everything reduces to Frobenius-root ideals. For
`J_f = √(f)`, the short exact sequence `0 → J_f → A → A ⧸ J_f → 0` and the flatness of `J_f`
(`TauCeti.flat_frobeniusRootIdeal`) reduce the vanishing to `Tor₁`, which holds because
`J_f ⊗[A] C → C` is injective (`TauCeti.frobeniusRootIdeal_subtype_rTensor_injective`); for this
case `C` only needs to be reduced. For two radical ideals `I` and `J`, the sum `I ⊔ J` is again
radical in a perfect ring, and the Mayer–Vietoris sequence
`0 → A ⧸ (I ⊓ J) → A ⧸ I × A ⧸ J → A ⧸ (I ⊔ J) → 0`
(`Submodule.shortExact_quotientInfSupShortComplex`) bounds `Tor` of `A ⧸ (I ⊔ J)` by `Tor` of
`A ⧸ I` and `A ⧸ J` and `Tor` in one degree lower of `A ⧸ (I ⊓ J)`, where `I ⊓ J` is again radical.
By induction on the degree this covers the radical of a finitely generated ideal, a finite sum of
Frobenius-root ideals, and a general radical ideal is the directed union of such radicals
(`Ideal.iSup_radical_fg`, `ModuleCat.isZero_Tor_succ_quotient_iSup`). In degree one, the
injectivity of `I ⊗[A] C → C` (`TauCeti.subtype_rTensor_injective_of_isRadical`) applies
directly.

## Main results

* `TauCeti.isZero_Tor_succ_quotient_frobeniusRootIdeal`: `Tor_{n+1}^A(A ⧸ J_f, C) = 0` for every
  reduced `A`-algebra `C`.
* `TauCeti.isZero_Tor_succ_quotient_of_isRadical`: `Tor_{n+1}^A(A ⧸ I, C) = 0` for every radical
  ideal `I` of `A` and every perfect `A`-algebra `C`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Lemma 3.16 and its proof.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u

variable {A : Type u} [CommRing A] {p : ℕ} [ExpChar A p] [PerfectRing A p] [Fact p.Prime]
  (C : Type u) [CommRing C] [Algebra A C]

/-- **Tor of the quotient by a Frobenius-root ideal.** For a Frobenius-root ideal `J_f = √(f)` of a
perfect ring `A` and a reduced `A`-algebra `C`, `Tor_{n+1}^A(A ⧸ J_f, C) = 0`. -/
theorem isZero_Tor_succ_quotient_frobeniusRootIdeal [IsReduced C] (f : A) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} A) (n + 1)).obj
      (ModuleCat.of A (A ⧸ frobeniusRootIdeal A p f))).obj (ModuleCat.of A C)) := by
  have hS := (frobeniusRootIdeal A p f).shortExact_quotientShortComplex
  cases n with
  | zero =>
    exact hS.isZero_Tor_one_X₃ _ (ModuleCat.isZero_Tor_succ_of_flat _ _ 0)
      (frobeniusRootIdeal_subtype_rTensor_injective C f)
  | succ n =>
    exact hS.isZero_Tor_succ_X₃ _ (ModuleCat.isZero_Tor_succ_of_flat _ _ _)
      (ModuleCat.isZero_Tor_succ_of_flat _ _ _)

/-- **Tor independence of radical quotients of perfect rings.** For a radical ideal `I` of a
perfect ring `A` and a perfect `A`-algebra `C`, `Tor_{n+1}^A(A ⧸ I, C) = 0`. -/
theorem isZero_Tor_succ_quotient_of_isRadical [ExpChar C p] [PerfectRing C p] {I : Ideal A}
    (hI : I.IsRadical) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} A) (n + 1)).obj (ModuleCat.of A (A ⧸ I))).obj
      (ModuleCat.of A C)) := by
  induction n generalizing I with
  | zero =>
    exact I.shortExact_quotientShortComplex.isZero_Tor_one_X₃ _
      (ModuleCat.isZero_Tor_succ_of_flat _ _ 0)
      (subtype_rTensor_injective_of_isRadical (p := p) C hI)
  | succ n ih =>
    have := isReduced_of_perfectRing C p
    -- The radical of a finitely generated ideal is a finite sum of Frobenius-root ideals.
    have fg {N : Ideal A} (hN : Submodule.FG N) : IsZero (((Tor (ModuleCat.{u} A) (n + 1 + 1)).obj
        (ModuleCat.of A (A ⧸ N.radical))).obj (ModuleCat.of A C)) := by
      induction N, hN using Submodule.fg_induction with
      | singleton f =>
        rw [← Ideal.span, ← frobeniusRootIdeal_eq_radical (p := p)]
        exact isZero_Tor_succ_quotient_frobeniusRootIdeal C f (n + 1)
      | sup N₁ N₂ _ _ h₁ h₂ =>
        have r₁ := Ideal.radical_isRadical N₁
        have r₂ := Ideal.radical_isRadical N₂
        rw [Ideal.radical_sup, (r₁.sup p r₂).radical]
        -- `Tor` of `A ⧸ √N₁ × A ⧸ √N₂` vanishes, and `Tor` of `A ⧸ (√N₁ ⊓ √N₂)` vanishes in one
        -- degree lower by induction.
        exact (Submodule.shortExact_quotientInfSupShortComplex (Ideal.radical N₁)
          (Ideal.radical N₂)).isZero_Tor_succ_X₃ _ (ModuleCat.isZero_Tor_prod _ h₁ h₂)
          (ih (r₁.inf r₂))
    -- A radical ideal is the directed union of the radicals of its finitely generated subideals.
    have : Nonempty {N : Ideal A // N.FG ∧ N ≤ I} := ⟨⟨⊥, Submodule.fg_bot, bot_le⟩⟩
    have key := ModuleCat.isZero_Tor_succ_quotient_iSup (M := ModuleCat.of A C)
      (X := ModuleCat.of A A) I.directed_radical_fg (n + 1) fun N ↦ fg N.2.1
    rwa [Ideal.iSup_radical_fg, hI.radical] at key

end TauCeti
