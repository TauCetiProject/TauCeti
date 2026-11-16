/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Local-ring and discrete-valuation-ring structure on fixed-point subrings

Let a monoid `G` act on a semiring `B` by semiring endomorphisms (`MulSemiringAction G B`).
If a fixed element `x` is a unit of `B`, its two-sided inverse is also fixed by `G`, by uniqueness
of inverses. Consequently the inclusion of the fixed subsemiring, fixed subring, or fixed
subalgebra into `B` is a local homomorphism (`IsLocalHom`), and whenever `B` is a local ring, so
are its fixed subsemiring, fixed subring, and fixed subalgebra.

When `B` is a discrete valuation ring, every ideal of the fixed subring `B^G` is principal: for a
nonzero ideal `I`, choosing an element `a ∈ I` minimizing `IsDiscreteValuationRing.addVal B`, any
`x ∈ I` satisfies `(a : B) ∣ (x : B)`, and cancellation in the domain `B` forces the quotient to be
`G`-invariant. If moreover `G` is a finite group, the product `∏ g : G, g • ϖ` of the translates of
a uniformizer `ϖ` of `B` is a nonzero nonunit fixed by `G`, so `B^G` is not a field and is
therefore a discrete valuation ring. The same holds for the fixed subalgebra
`FixedPoints.subalgebra A B G` over any commutative base ring `A` commuting with `G`.

## Main results

* `TauCeti.FixedPoints.instIsLocalHomSubsemiringSubtype`,
  `TauCeti.FixedPoints.instIsLocalHomSubringSubtype`,
  `TauCeti.FixedPoints.instIsLocalHomSubalgebraVal`,
  `TauCeti.FixedPoints.instIsLocalHomAlgebraMapSubalgebra`,
  `TauCeti.FixedPoints.instIsLocalHomAlgebraMapLeft`: inclusions of fixed-point subobjects are
  local homomorphisms, and a local algebra map into `B` remains local into `FixedPoints.subalgebra`.
* `TauCeti.FixedPoints.instIsLocalRingSubsemiring`,
  `TauCeti.FixedPoints.instIsLocalRingSubring`,
  `TauCeti.FixedPoints.instIsLocalRingSubalgebra`: fixed points in a local ring form a local ring.
* `TauCeti.FixedPoints.instIsPrincipalIdealRingSubring`,
  `TauCeti.FixedPoints.instIsPrincipalIdealRingSubalgebra`: fixed points of any monoid action on a
  discrete valuation ring form a principal ideal ring.
* `TauCeti.FixedPoints.instIsDiscreteValuationRingSubring`,
  `TauCeti.FixedPoints.instIsDiscreteValuationRingSubalgebra`: fixed points of a finite group
  action on a discrete valuation ring form a discrete valuation ring.
-/

public section

namespace TauCeti.FixedPoints

section LocalRing

/-- The inclusion of the fixed subsemiring of a monoid action is a local homomorphism: if a fixed
element is a unit in the ambient semiring, its inverse is again fixed. -/
instance instIsLocalHomSubsemiringSubtype {B G : Type*} [Semiring B] [Monoid G]
    [MulSemiringAction G B] : IsLocalHom (FixedPoints.subsemiring B G).subtype where
  map_nonunit x hx := by
    obtain ⟨u, hu⟩ := hx
    have hinv : (↑u⁻¹ : B) ∈ FixedPoints.subsemiring B G := fun g ↦ by
      calc
        g • (↑u⁻¹ : B) = (g • (↑u⁻¹ : B)) * ((u : B) * (↑u⁻¹ : B)) := by
          rw [Units.mul_inv, mul_one]
        _ = (g • (↑u⁻¹ : B)) * (g • (u : B)) * (↑u⁻¹ : B) := by
          rw [← mul_assoc, hu, Subsemiring.coe_subtype, x.2 g]
        _ = g • ((↑u⁻¹ : B) * (u : B)) * (↑u⁻¹ : B) := by
          rw [smul_mul']
        _ = (↑u⁻¹ : B) := by
          rw [Units.inv_mul, smul_one, one_mul]
    exact isUnit_iff_exists.2 ⟨⟨↑u⁻¹, hinv⟩,
      Subtype.ext (by simp [hu]), Subtype.ext (by simp [hu])⟩

/-- The inclusion of the fixed subring of a monoid action is a local homomorphism. -/
instance instIsLocalHomSubringSubtype {B G : Type*} [Ring B] [Monoid G]
    [MulSemiringAction G B] : IsLocalHom (FixedPoints.subring B G).subtype :=
  inferInstanceAs (IsLocalHom (FixedPoints.subsemiring B G).subtype)

/-- The inclusion of the fixed subalgebra of a monoid action is a local homomorphism. -/
instance instIsLocalHomSubalgebraVal {A B G : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalHom (FixedPoints.subalgebra A B G).val.toRingHom :=
  inferInstanceAs (IsLocalHom (FixedPoints.subsemiring B G).subtype)

/-- For a commutative semiring `B`, the algebra map `FixedPoints.subalgebra A B G → B` is a local
homomorphism. -/
instance instIsLocalHomAlgebraMapSubalgebra {A B G : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalHom (algebraMap (FixedPoints.subalgebra A B G) B) :=
  inferInstanceAs (IsLocalHom (FixedPoints.subsemiring B G).subtype)

/-- If `A → B` is a local homomorphism, so is `A → FixedPoints.subalgebra A B G`. -/
instance instIsLocalHomAlgebraMapLeft {A B G : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    [IsLocalHom (algebraMap A B)] :
    IsLocalHom (algebraMap A (FixedPoints.subalgebra A B G)) := by
  have hcomp : (FixedPoints.subalgebra A B G).val.toRingHom.comp
      (algebraMap A (FixedPoints.subalgebra A B G)) = algebraMap A B := by
    ext a
    rfl
  have : IsLocalHom ((FixedPoints.subalgebra A B G).val.toRingHom.comp
      (algebraMap A (FixedPoints.subalgebra A B G))) := hcomp ▸ ‹_›
  exact isLocalHom_of_comp (algebraMap A (FixedPoints.subalgebra A B G))
    (FixedPoints.subalgebra A B G).val.toRingHom

/-- The fixed subsemiring of a monoid action on a local semiring is local. -/
instance instIsLocalRingSubsemiring {B G : Type*} [Semiring B] [IsLocalRing B] [Monoid G]
    [MulSemiringAction G B] : IsLocalRing (FixedPoints.subsemiring B G) :=
  (FixedPoints.subsemiring B G).subtype.domain_isLocalRing

/-- The fixed subring of a monoid action on a local ring is local. -/
instance instIsLocalRingSubring {B G : Type*} [Ring B] [IsLocalRing B] [Monoid G]
    [MulSemiringAction G B] : IsLocalRing (FixedPoints.subring B G) :=
  (FixedPoints.subring B G).subtype.domain_isLocalRing

/-- The fixed subalgebra of a monoid action on a local semiring is local. -/
instance instIsLocalRingSubalgebra {A B G : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    [IsLocalRing B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalRing (FixedPoints.subalgebra A B G) :=
  (FixedPoints.subalgebra A B G).val.toRingHom.domain_isLocalRing

end LocalRing

section DiscreteValuationRing

/-- The fixed subring of any monoid action on a discrete valuation ring is a principal ideal ring:
every nonzero ideal is generated by an element minimizing the ambient additive valuation. -/
instance instIsPrincipalIdealRingSubring {B G : Type*} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Monoid G] [MulSemiringAction G B] :
    IsPrincipalIdealRing (FixedPoints.subring B G) where
  principal I := by
    classical
    by_cases hI : I = ⊥
    · exact ⟨0, by simp [hI]⟩
    obtain ⟨x₀, hx₀I, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hx₀' : (x₀ : B) ≠ 0 := by simpa using hx₀
    have hne : ∃ n : ℕ, ∃ a ∈ I, IsDiscreteValuationRing.addVal B (a : B) = n := by
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1
        (IsDiscreteValuationRing.addVal_eq_top_iff.not.2 hx₀')
      exact ⟨n, x₀, hx₀I, hn.symm⟩
    set m := Nat.find hne
    obtain ⟨a, haI, ham⟩ := Nat.find_spec hne
    have ha0 : (a : B) ≠ 0 :=
      IsDiscreteValuationRing.addVal_eq_top_iff.not.1 (ham ▸ ENat.natCast_ne_top m)
    refine ⟨a, le_antisymm (fun x hx ↦ ?_) ((Ideal.span_singleton_le_iff_mem I).2 haI)⟩
    rw [Ideal.mem_span_singleton]
    by_cases hx0 : x = 0
    · exact hx0 ▸ dvd_zero a
    have hx0' : (x : B) ≠ 0 := by simpa using hx0
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1
      (IsDiscreteValuationRing.addVal_eq_top_iff.not.2 hx0')
    have hmk : m ≤ k := Nat.find_min' hne ⟨x, hx, hk.symm⟩
    have hdvd : (a : B) ∣ (x : B) := by
      rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, ham, ← hk]
      exact_mod_cast hmk
    obtain ⟨c, hc⟩ := hdvd
    have hc_fix : c ∈ FixedPoints.subring B G := fun g ↦
      mul_left_cancel₀ ha0 <| by
        calc
          (a : B) * (g • c) = (g • (a : B)) * (g • c) := by rw [a.2 g]
          _ = g • ((a : B) * c) := (smul_mul' g (a : B) c).symm
          _ = (x : B) := by rw [← hc, x.2 g]
          _ = (a : B) * c := hc
    exact ⟨⟨c, hc_fix⟩, Subtype.ext hc⟩

/-- The fixed subalgebra of any monoid action on a discrete valuation ring is a principal ideal
ring. -/
instance instIsPrincipalIdealRingSubalgebra {A B G : Type*} [CommRing A] [CommRing B]
    [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Monoid G] [MulSemiringAction G B]
    [SMulCommClass G A B] : IsPrincipalIdealRing (FixedPoints.subalgebra A B G) :=
  inferInstanceAs (IsPrincipalIdealRing (FixedPoints.subring B G))

/-- The fixed subring of a finite group action on a discrete valuation ring is a discrete
valuation ring: the product of the `G`-translates of a uniformizer is a nonzero nonunit fixed by
`G`, so the local principal ideal domain `B^G` is not a field. -/
instance instIsDiscreteValuationRingSubring {B G : Type*} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Group G] [Finite G] [MulSemiringAction G B] :
    IsDiscreteValuationRing (FixedPoints.subring B G) where
  not_a_field' := by
    have := Fintype.ofFinite G
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
    let x : B := ∏ g : G, g • ϖ
    have hx_fix : x ∈ FixedPoints.subring B G := Finset.smul_prod_perm ϖ
    have hx_ne : (⟨x, hx_fix⟩ : FixedPoints.subring B G) ≠ 0 := by
      intro h0
      have hx0 : x = 0 := congrArg Subtype.val h0
      obtain ⟨g, -, hg⟩ := Finset.prod_eq_zero_iff.1 hx0
      exact hϖ.ne_zero (by simpa [inv_smul_smul] using congrArg (g⁻¹ • ·) hg)
    have hx_not_unit : ¬ IsUnit (⟨x, hx_fix⟩ : FixedPoints.subring B G) := fun hu ↦ by
      have huB : IsUnit x := hu.map (FixedPoints.subring B G).subtype
      have hdvd : ϖ ∣ x := by
        simpa only [one_smul] using Finset.dvd_prod_of_mem (fun g : G ↦ g • ϖ) (Finset.mem_univ 1)
      exact hϖ.not_isUnit (isUnit_of_dvd_unit hdvd huB)
    intro hbot
    have hmem : (⟨x, hx_fix⟩ : FixedPoints.subring B G) ∈
        IsLocalRing.maximalIdeal (FixedPoints.subring B G) :=
      (IsLocalRing.mem_maximalIdeal _).2 hx_not_unit
    rw [hbot, Ideal.mem_bot] at hmem
    exact hx_ne hmem

/-- The fixed subalgebra of a finite group action on a discrete valuation ring is a discrete
valuation ring. -/
instance instIsDiscreteValuationRingSubalgebra {A B G : Type*} [CommRing A] [CommRing B]
    [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] :
    IsDiscreteValuationRing (FixedPoints.subalgebra A B G) :=
  inferInstanceAs (IsDiscreteValuationRing (FixedPoints.subring B G))

end DiscreteValuationRing

end TauCeti.FixedPoints
