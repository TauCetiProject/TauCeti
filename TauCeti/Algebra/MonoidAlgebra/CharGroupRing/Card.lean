/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Presentation.Card
public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Lattice
public import TauCeti.RingTheory.Ideal.Quotient.Pi
public import TauCeti.RingTheory.Subring.FiniteIndex
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import TauCeti.RingTheory.Ideal.Quotient.Regular
import TauCeti.SetTheory.Cardinal.Finite
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Regular.Pi
import Mathlib.Data.ZMod.QuotientRing

/-!
# The order of principal quotients and quadratically presented modules over character group rings

Let `G` be a finite commutative group, `O` an integral domain in which `#G ≠ 0`, and
`Ψ : Set (G →* Oˣ)` a set of characters with character group ring `R_Ψ = Set.charGroupRing Ψ`.
Following Dasgupta and Kakde (Lemma 2.5), for any `x ∈ nonZeroDivisors (charGroupRing Ψ)`, if
`O ⧸ (#G)` is finite then `R_Ψ` has finite additive index in `Ψ → O`, `x` remains a non-zero-divisor
in `Ψ → O` (`Set.charGroupRing.mem_nonZeroDivisors_iff`), and comparing principal quotients via
`Subring.natCard_quotient_span_singleton`, `Ideal.quotientSpanSingletonPiEquiv`, and the
multiplicativity of principal-quotient cardinalities (`Ideal.natCard_quotient_span_singleton_prod`)
yields
`Nat.card (charGroupRing Ψ ⧸ Ideal.span {x}) = Nat.card (O ⧸ Ideal.span {∏ ψ : Ψ, (x : Ψ → O) ψ})`
(`Set.charGroupRing.card_quotient_span`).

Notice that neither `[IsDedekindDomain O]`, `[Infinite O]`, nor `[Ring.HasFiniteQuotients O]` is
required for the cardinality equality once `[Finite (O ⧸ Ideal.span {(Nat.card G : O)})]` holds, so
the theorem applies directly to orders in number fields (where `Ring.HasFiniteQuotients O` holds;
see `Set.charGroupRing.finite_quotient_span_of_hasFiniteQuotients`) as well as to discrete valuation
rings with finite residue field such as `ℤ_p` and its finite extensions.

When `O` is a principal ideal domain, combining Lemma 2.5 with Lemma 2.4
(`TauCeti.IsQuadraticallyPresented.card_eq`) expresses the order of any quadratically presented
`R_Ψ`-module `N` with `Fitt₀(N) = (x)` (`x ∈ R_Ψ⁰`) directly in `O` as
`Nat.card N = Nat.card (O ⧸ Ideal.span {∏ ψ : Ψ, (x : Ψ → O) ψ})`
(`Set.charGroupRing.card_module_of_fittingIdeal_eq_span`).

## Main results

* `Set.charGroupRing.card_quotient_span`: Dasgupta–Kakde Lemma 2.5,
  `Nat.card (R_Ψ ⧸ (x)) = Nat.card (O ⧸ (∏ ψ : Ψ, x ψ))`.
* `Set.charGroupRing.finite_quotient_span_iff`,
  `Set.charGroupRing.finite_quotient_span_of_hasFiniteQuotients`: finiteness criteria for
  `R_Ψ ⧸ Ideal.span {x}`.
* `Set.charGroupRing.card_module_of_fittingIdeal_eq_span`: combined cardinality formula for a
  quadratically presented `R_Ψ`-module with regular generator `x` of `Fitt₀(N)`.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023),
  Lemmas 2.4 and 2.5.
-/

public section

namespace Set.charGroupRing

section Domain

variable {O G : Type*} [CommRing O] [IsDomain O] [CommGroup G] [Finite G]

/-- **The order of a principal quotient of a character group ring** (Dasgupta–Kakde, Lemma 2.5).
Let `O` be an integral domain in which `#G ≠ 0` and `O ⧸ (#G)` is finite. For any
`x ∈ nonZeroDivisors (charGroupRing Ψ)`, the quotient `charGroupRing Ψ ⧸ Ideal.span {x}` has the
same `Nat.card` as `O ⧸ Ideal.span {∏ ψ : Ψ, (x : Ψ → O) ψ}` (`0` when infinite). -/
theorem card_quotient_span [Finite (O ⧸ Ideal.span {(Nat.card G : O)})]
    (hG : (Nat.card G : O) ≠ 0) {Ψ : Set (G →* Oˣ)} [Fintype Ψ]
    {x : charGroupRing Ψ} (hx : x ∈ nonZeroDivisors (charGroupRing Ψ)) :
    Nat.card (charGroupRing Ψ ⧸ Ideal.span {x}) =
      Nat.card (O ⧸ Ideal.span {∏ ψ : Ψ, (x : Ψ → O) ψ}) := by
  have hcoord : ∀ ψ : Ψ, (x : Ψ → O) ψ ≠ 0 := (mem_nonZeroDivisors_iff Ψ hG x).mp hx
  have hx_pi : (x : Ψ → O) ∈ nonZeroDivisors (Ψ → O) :=
    (Pi.isRegular_iff.mpr fun ψ ↦ isRegular_iff_ne_zero.mpr (hcoord ψ)).mem_nonZeroDivisors
  calc Nat.card (charGroupRing Ψ ⧸ Ideal.span {x})
      = Nat.card ((Ψ → O) ⧸ Ideal.span {(x : Ψ → O)}) :=
        (charGroupRing Ψ).toSubring.natCard_quotient_span_singleton hx_pi
    _ = ∏ ψ : Ψ, Nat.card (O ⧸ Ideal.span {(x : Ψ → O) ψ}) := by
        rw [Nat.card_congr (Ideal.quotientSpanSingletonPiEquiv (x : Ψ → O)).toEquiv, Nat.card_pi]
    _ = Nat.card (O ⧸ Ideal.span {∏ ψ : Ψ, (x : Ψ → O) ψ}) :=
        (Ideal.natCard_quotient_span_singleton_prod Finset.univ (x : Ψ → O) fun ψ _ ↦
          mem_nonZeroDivisors_of_ne_zero (hcoord ψ)).symm

/-- Under the hypotheses of `card_quotient_span`, `charGroupRing Ψ ⧸ Ideal.span {x}` is finite if
and only if `O ⧸ Ideal.span {∏ ψ : Ψ, (x : Ψ → O) ψ}` is finite. -/
theorem finite_quotient_span_iff [Finite (O ⧸ Ideal.span {(Nat.card G : O)})]
    (hG : (Nat.card G : O) ≠ 0) {Ψ : Set (G →* Oˣ)} [Fintype Ψ]
    {x : charGroupRing Ψ} (hx : x ∈ nonZeroDivisors (charGroupRing Ψ)) :
    Finite (charGroupRing Ψ ⧸ Ideal.span {x}) ↔
      Finite (O ⧸ Ideal.span {∏ ψ : Ψ, (x : Ψ → O) ψ}) :=
  TauCeti.finite_iff_of_natCard_eq (card_quotient_span hG hx)

/-- Over an integral domain with `Ring.HasFiniteQuotients O` in which `#G ≠ 0`, every principal
quotient `charGroupRing Ψ ⧸ Ideal.span {x}` by a non-zero-divisor `x` is finite. -/
theorem finite_quotient_span_of_hasFiniteQuotients [Ring.HasFiniteQuotients O]
    (hG : (Nat.card G : O) ≠ 0) {Ψ : Set (G →* Oˣ)}
    {x : charGroupRing Ψ} (hx : x ∈ nonZeroDivisors (charGroupRing Ψ)) :
    Finite (charGroupRing Ψ ⧸ Ideal.span {x}) := by
  classical
  let _ : Fintype Ψ := Fintype.ofFinite Ψ
  have : Finite (O ⧸ Ideal.span {(Nat.card G : O)}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hG)
  have hcoord : ∀ ψ : Ψ, (x : Ψ → O) ψ ≠ 0 := (mem_nonZeroDivisors_iff Ψ hG x).mp hx
  have hprod : ∏ ψ : Ψ, (x : Ψ → O) ψ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ψ _ ↦ hcoord ψ
  have : Finite (O ⧸ Ideal.span {∏ ψ : Ψ, (x : Ψ → O) ψ}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hprod)
  exact (finite_quotient_span_iff hG hx).mpr ‹_›

end Domain

section PrincipalIdealRing

variable {O G : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  [CommGroup G] [Finite G]

/-- **Combined module-order formula over a character group ring** (Dasgupta–Kakde, Lemmas 2.4–2.5).
Let `O` be a principal ideal domain in which `#G ≠ 0` and `O ⧸ (#G)` is finite. If `N` is a
quadratically presented `charGroupRing Ψ`-module with `Fitt₀(N) = Ideal.span {x}` for
`x ∈ nonZeroDivisors (charGroupRing Ψ)`, then
`Nat.card N = Nat.card (O ⧸ Ideal.span {∏ ψ : Ψ, (x : Ψ → O) ψ})`. -/
theorem card_module_of_fittingIdeal_eq_span [Finite (O ⧸ Ideal.span {(Nat.card G : O)})]
    (hG : (Nat.card G : O) ≠ 0) {Ψ : Set (G →* Oˣ)} [Fintype Ψ]
    {N : Type*} [AddCommGroup N] [Module (charGroupRing Ψ) N] [Module.Finite (charGroupRing Ψ) N]
    (hP : TauCeti.IsQuadraticallyPresented (charGroupRing Ψ) N)
    {x : charGroupRing Ψ} (hx : x ∈ nonZeroDivisors (charGroupRing Ψ))
    (hfitt : TauCeti.fittingIdeal (charGroupRing Ψ) N 0 = Ideal.span {x}) :
    Nat.card N = Nat.card (O ⧸ Ideal.span {∏ ψ : Ψ, (x : Ψ → O) ψ}) := by
  have hcard : Nat.card N = Nat.card ((charGroupRing Ψ).toSubring ⧸ Ideal.span {x}) :=
    hP.card_eq (S := (charGroupRing Ψ).toSubring) hx hfitt
  exact hcard.trans (card_quotient_span hG hx)

-- Over a principal ideal domain, `charGroupRing Ψ` is automatically a finite free `O`-module via
-- Mathlib's `Module.free_of_finite_type_torsion_free'`.
example (Ψ : Set (G →* Oˣ)) : Module.Free O (charGroupRing Ψ) := inferInstance

end PrincipalIdealRing

section Examples

-- For `G = ℤˣ` (`#G = 2`) over `O = ℤ` and both characters `Ψ = {1, id}`, `R_Ψ ≅ ℤ[C₂]` is a
-- proper index-`2` order in `ℤ × ℤ`, and the non-diagonal element `x = α_Ψ(2 + [-1])` evaluates
-- to `3` at `1` and `1` at `id`, so `Nat.card (R_Ψ ⧸ (x)) = 3 * 1 = 3` (index `2` cancels).
example :
    let Ψ : Set (ℤˣ →* ℤˣ) := {1, MonoidHom.id ℤˣ}
    let x : charGroupRing Ψ :=
      proj Ψ (MonoidAlgebra.single 1 2 + MonoidAlgebra.single (-1 : ℤˣ) 1)
    Nat.card (charGroupRing Ψ ⧸ Ideal.span {x}) = 3 := by
  classical
  intro Ψ x
  let _ : Fintype Ψ := Fintype.ofFinite Ψ
  have hG : (Nat.card ℤˣ : ℤ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have _ : Finite (ℤ ⧸ Ideal.span {(Nat.card ℤˣ : ℤ)}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hG)
  have hne : (1 : ℤˣ →* ℤˣ) ≠ MonoidHom.id ℤˣ :=
    fun h ↦ absurd (DFunLike.congr_fun h (-1 : ℤˣ)) (by decide)
  have hx : x ∈ nonZeroDivisors (charGroupRing Ψ) := by
    rw [mem_nonZeroDivisors_iff Ψ hG]
    rintro ⟨ψ, rfl | rfl⟩ <;> simp [x]
  let f : Bool → Ψ
    | false => ⟨1, .inl rfl⟩
    | true => ⟨MonoidHom.id ℤˣ, .inr rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab ↦ ?_, ?_⟩
    · cases a <;> cases b
      · rfl
      · exact (hne (congrArg Subtype.val hab)).elim
      · exact (hne (congrArg Subtype.val hab).symm).elim
      · rfl
    · rintro ⟨ψ, rfl | rfl⟩
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  let e : Bool ≃ Ψ := Equiv.ofBijective f hf
  have hprod : ∏ ψ : Ψ, (x : Ψ → ℤ) ψ = ((3 : ℕ) : ℤ) := by
    rw [← e.prod_comp, Fintype.prod_bool]
    simp [e, f, x]
  rw [card_quotient_span hG hx, hprod,
    Nat.card_congr (Int.quotientSpanNatEquivZMod 3).toEquiv, Nat.card_zmod]

end Examples

end Set.charGroupRing
