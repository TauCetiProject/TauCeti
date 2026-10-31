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

import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.RingTheory.Perfect.PerfectClosure

/-!
# Tor independence of perfect rings

Let `A` be a perfect ring of prime characteristic `p` and let `B` and `C` be perfect `A`-algebras.
We show that `Tor_i^A(B, C) = 0` for every `i > 0`, with `Tor` Mathlib's `CategoryTheory.Tor` in
`ModuleCat A` (`TauCeti.isZero_Tor_succ_of_perfectRing`). Thus the derived tensor product of `B`
and `C` over `A` is concentrated in degree zero, where it is `B ⊗[A] C`. All three rings must be
perfect: over the perfect ring `(k[x, y] ⧸ (x y))_perf`, the non-perfect quotients by `x` and by
`y` have nonzero `Tor₂` (Bhatt and Scholze, Remark 11.33).

The main case is `B = A ⧸ I` for a radical ideal `I` of `A`
(`TauCeti.isZero_Tor_succ_quotient_of_isRadical`). The general case reduces to it by presenting
`B` as the quotient of the perfect polynomial algebra `P = A[X_b ^ (1 / p ^ ∞) : b ∈ B]` by a
radical ideal (`TauCeti.exists_surjective_perfectClosure_mvPolynomial`). Since `P` is flat over `A`
(`TauCeti.flat_perfectClosureOf_comp_C`), flat base change identifies the vanishing of
`Tor_i^A(B, C)` with that of `Tor_i^P(B, P ⊗[A] C)` (`ModuleCat.isZero_Tor_restrictScalars_iff`),
and `P ⊗[A] C` is a perfect `P`-algebra (`Algebra.TensorProduct.perfectRing`).

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
* `TauCeti.isZero_Tor_succ_of_perfectRing`: `Tor_{n+1}^A(B, C) = 0` for all perfect `A`-algebras
  `B` and `C`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Lemma 3.16 and its proof, and Remark 11.33.
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

namespace TauCeti

universe u

variable {A : Type u} [CommRing A] {p : ℕ} [ExpChar A p] [PerfectRing A p] [Fact p.Prime]

section Quotient

variable (C : Type u) [CommRing C] [Algebra A C]

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

end Quotient

/-- **Tor independence of perfect rings.** For perfect algebras `B` and `C` over a perfect ring `A`
of prime characteristic `p`, `Tor_{n+1}^A(B, C) = 0`. -/
theorem isZero_Tor_succ_of_perfectRing (B C : Type u) [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] [ExpChar B p] [PerfectRing B p] [ExpChar C p] [PerfectRing C p] (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} A) (n + 1)).obj (ModuleCat.of A B)).obj (ModuleCat.of A C)) := by
  have hp := (Fact.out : p.Prime)
  have : CharP A p := (expChar_prime_iff (R := A) hp).1 inferInstance
  have : CharP B p := (expChar_prime_iff (R := B) hp).1 inferInstance
  -- Present `B` as the quotient of a perfect polynomial algebra `P`, flat over `A`, by a radical
  -- ideal.
  let P := PerfectClosure (MvPolynomial B A) p
  let f : A →+* P := (PerfectClosure.of (MvPolynomial B A) p).comp MvPolynomial.C
  obtain ⟨g, hg, hgf, hker⟩ := exists_surjective_perfectClosure_mvPolynomial p (algebraMap A B)
  let e := RingHom.quotientKerEquivOfSurjective hg
  have he (a : A) (b : B) : e.symm (a • b) = f a • e.symm b := by
    rw [Algebra.smul_def, ← RingHom.congr_fun hgf a, RingHom.comp_apply, map_mul,
      RingHom.quotientKerEquivOfSurjective_symm_apply, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
  let eB : B ≃ₗ[A] (ModuleCat.restrictScalars f).obj (ModuleCat.of P (P ⧸ RingHom.ker g)) :=
    { e.symm.toAddEquiv with map_smul' := he }
  refine IsZero.of_iso ?_ (((Tor (ModuleCat.{u} A) (n + 1)).mapIso eB.toModuleIso).app _)
  -- By flat base change it suffices to show `Tor_{n+1}^P(P ⧸ ker g, P ⊗[A] C) = 0`.
  rw [ModuleCat.isZero_Tor_restrictScalars_iff f (flat_perfectClosureOf_comp_C A B p)]
  let := f.toAlgebra
  refine IsZero.of_iso ?_ (((Tor (ModuleCat.{u} P) (n + 1)).obj _).mapIso
    (ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of A C)))
  rcases subsingleton_or_nontrivial (P ⊗[A] C) with _ | _
  · have := (ModuleCat.isZero_of_subsingleton (ModuleCat.of P (P ⊗[A] C))).projective
    exact isZero_Tor_succ_of_projective (ModuleCat.{u} P) _ (ModuleCat.of P (P ⊗[A] C)) n
  -- `P ⊗[A] C` is a nonzero `A`-algebra, so it has characteristic `p`, and it is perfect.
  have : CharP (P ⊗[A] C) p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (algebraMap A (P ⊗[A] C)), CharP.cast_eq_zero, map_zero]
  exact isZero_Tor_succ_quotient_of_isRadical (p := p) (P ⊗[A] C) hker n

end TauCeti
