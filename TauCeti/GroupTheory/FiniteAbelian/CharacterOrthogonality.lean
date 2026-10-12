/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
-- Non-public: `unitsEquivNeZero` reindexes a punctured field sum by its units.
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Character orthogonality for finite commutative groups

For a finite commutative group `G` and a domain `M` with enough roots of unity, the characters
of `G` are the monoid homomorphisms `G →* Mˣ`. This file records the *column* orthogonality
relation — the one summed over the character group — in both its punctured and its normal form,
and shows that the commutativity it assumes is necessary: the column relation fails for every
finite non-commutative group whenever the number of characters is nonzero in `M`, as it is in
characteristic zero. The underlying group-theoretic fact, that homomorphisms into a
commutative monoid separate elements only in a commutative group, is
`TauCeti.isMulCommutative_of_forall_exists_monoidHom_apply_ne_one` in
`TauCeti.GroupTheory.Commutator`.

## Main results

* `CommGroup.sum_monoidHom_apply_eq_zero_of_ne_one`: for `g ≠ 1`, the sum `∑ χ : G →* Mˣ, χ g`
  over all characters vanishes.
* `CommGroup.sum_monoidHom_apply_eq_ite`: the same sum in normal form, `Nat.card G` at `g = 1`
  and `0` elsewhere. This is the shape an indicator-formula consumer wants, and it is the `simp`
  normal form for such a sum.
* `CommGroup.sum_monoidHom_apply_eq_ite`'s tagged form,
  `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite`: summing `(χ σ)⁻¹ * χ g` isolates the single
  element `σ`, giving `Nat.card G` when `g = σ` and `0` otherwise.
* `AddChar.sum_units_mul_eq_neg_one`: a nontrivial additive character of a finite field
  sums to `-1` over the nonzero elements, even after multiplication by a unit.
* `TauCeti.sum_monoidHom_apply_eq_card_of_mem_commutator`: at an element of the commutator
  subgroup the character sum is the number of characters, every summand being `1`.
* `TauCeti.exists_sum_inv_mul_monoidHom_apply_ne_ite`: **column orthogonality fails for every
  finite non-commutative group** whenever the number of characters is nonzero in `M`, as in
  characteristic zero: at the tag `1` and a nontrivial commutator the tagged sum is the number
  of characters, not `0`.

The file also registers `Fintype (G →* Mˣ)`, which Mathlib leaves at `Finite`; without it a
consumer's own character sum does not elaborate, and two ad-hoc `Fintype.ofFinite` introductions
give syntactically distinct sums. That instance needs only `LeftCancelMonoid G`, so it also serves
consumers indexing over the characters of a finite noncommutative group or monoid.

## Row orthogonality and punctured additive-character sums

The companion *row* relation — for a nontrivial `χ : G →* Mˣ`, the sum `∑ g : G, χ g` over the
group vanishes — is already `sum_hom_units_eq_zero` in
`Mathlib/RingTheory/IntegralDomain.lean`, which states exactly that for an arbitrary monoid
homomorphism `G →* R` into a domain. Specialising it to a character is
`sum_hom_units_eq_zero ((Units.coeHom M).comp χ)`, i.e. the Mathlib lemma composed with the
unit coercion and nothing else, so no declaration for it is added. Callers wanting the row
relation should use the Mathlib lemma directly. (`MulChar.sum_eq_zero_of_ne_one` in
`Mathlib/NumberTheory/MulChar/Basic.lean` is the analogous statement in the `MulChar`
vocabulary, for a multiplicative character of a finite commutative monoid valued in a domain.)

The theorem `AddChar.sum_units_mul_eq_neg_one` below is not a restatement of that full row
relation: it removes the zero term from a finite-field additive-character sum and reindexes the
remaining nonzero elements by `Fˣ`. This punctured form is what character computations over a
finite field consume directly.

The column relation genuinely is not in Mathlib in this generality. It appears there only in
specialisations: the `ZMod n` one, `DirichletCharacter.sum_characters_eq_zero` in
`Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean`, and the finite-additive-group one
over `ℂ`, `AddChar.sum_apply_eq_ite` in
`Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean` (with
`AddChar.sum_apply_eq_zero_iff_ne_zero` beside it). Neither implies the statement below, which is
multiplicative and valued in an arbitrary domain with enough roots of unity rather than in `ℂ`
or over `ZMod n`.

## References

Two of the results are adapted from
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca).

* `CommGroup.sum_monoidHom_apply_eq_zero_of_ne_one` comes from `sum_char_apply_eq_zero_of_ne_one`
  in `CebotarevDensity/ForMathlib/CharacterOrthogonality.lean`, at commit
  `8575c9df1ae0a61120ab5c964c7911414254bec7`.
* `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` comes from the private
  `sum_galoisCharacter_mul_inv_eq` in `CebotarevDensity/Cyclotomic.lean`, at commit
  `55a89985d47a3befcf6069aca1da250ff088b5c7`, where the argument is attributed to Sharifi,
  *Algebraic Number Theory*, 7.2.1 step (iii), p. 142. The source writes the sum as
  `∑ χ, χ σ * (χ τ)⁻¹` with the inverse on the second argument and concludes `σ * τ⁻¹ = 1`; the
  statement here carries the inverse on the tag and concludes `g = σ`, which is the same identity
  read in the other orientation.
-/

public section

open scoped commutatorElement

namespace AddChar

variable {F : Type*} [Field F] [Fintype F]
variable {R : Type*} [CommRing R] [IsDomain R]

open scoped Classical in
/-- A nontrivial additive character of a finite field sums to `-1` over the units, even after
multiplication by a fixed unit. This is the punctured form of
`AddChar.sum_eq_zero_of_ne_one`. -/
theorem sum_units_mul_eq_neg_one (ψ : AddChar F R) (hψ : ψ ≠ 1) (c : Fˣ) :
    ∑ d : Fˣ, ψ ((c : F) * (d : F)) = -1 := by
  have hsum : ∑ x : F, ψ ((c : F) * x) = 0 := by
    simpa [AddChar.mulShift_apply] using
      AddChar.sum_eq_zero_of_ne_one ((AddChar.IsPrimitive.of_ne_one hψ) c.ne_zero)
  have hnonzero : ∑ x : {x : F // x ≠ 0}, ψ ((c : F) * (x : F)) = -1 := by
    have hall := (Equiv.sumCompl (fun x : F => x = 0)).sum_comp
      (fun x : F => ψ ((c : F) * x))
    rw [Fintype.sum_sum_type] at hall
    have hall' :
        (∑ x : {x : F // x = 0}, ψ ((c : F) * (x : F))) +
          ∑ x : {x : F // x ≠ 0}, ψ ((c : F) * (x : F)) =
            ∑ x : F, ψ ((c : F) * x) := by
      simpa only [Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr] using hall
    have hval_zero (x : {x : F // x = 0}) : (x : F) = 0 := x.2
    have heqzero : ∑ x : {x : F // x = 0}, ψ ((c : F) * (x : F)) = 1 := by
      simp_rw [hval_zero]
      simp
    rw [hsum, heqzero] at hall'
    exact eq_neg_of_add_eq_zero_right hall'
  rw [← hnonzero]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ fun d => rfl

end AddChar

variable {G : Type*} [Finite G] {M : Type*} [CommRing M] [IsDomain M]

/-- The characters of a finite left-cancellative monoid valued in a domain form a `Fintype`.
Mathlib registers only `Finite (G →* Mˣ)`, so a character sum written by a consumer has no
`Finset` to range over without this; it mirrors `AddChar.instFintype`. Neither commutativity nor
invertibility is needed: `Finite (G →* Mˣ)` already holds at `LeftCancelMonoid`, which is where
this is stated. -/
noncomputable instance instFintypeMonoidHomUnits [LeftCancelMonoid G] : Fintype (G →* Mˣ) :=
  Fintype.ofFinite _

namespace CommGroup

variable [CommGroup G] [HasEnoughRootsOfUnity M (Monoid.exponent G)]

/-- **Character-column orthogonality** for a finite commutative group `G` valued in a domain `M`
with enough roots of unity: for `g ≠ 1`, the sum of `χ g` over all characters `χ : G →* Mˣ`
vanishes. -/
theorem sum_monoidHom_apply_eq_zero_of_ne_one {g : G} (hg : g ≠ 1) :
    ∑ χ : G →* Mˣ, (χ g : M) = 0 := by
  -- A specialisation of `sum_hom_units_eq_zero` on the dual group `G →* Mˣ` along the
  -- evaluation homomorphism `χ ↦ χ g`.
  obtain ⟨χ₀, hχ₀⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity G M hg
  exact sum_hom_units_eq_zero ((Units.coeHom M).comp (MonoidHom.eval g))
    fun h ↦ hχ₀ <| Units.val_eq_one.mp <| DFunLike.congr_fun h χ₀

/-- **Column orthogonality in normal form**: the character sum is `Nat.card G` at the identity
and vanishes elsewhere. This covers both cases at once, and states the identity value as the
cardinality of `G` itself rather than of its dual, which is the shape an indicator-formula
consumer wants. -/
@[simp]
theorem sum_monoidHom_apply_eq_ite [DecidableEq G] (g : G) :
    ∑ χ : G →* Mˣ, (χ g : M) = if g = 1 then (Nat.card G : M) else 0 := by
  split
  · next hg =>
    subst hg
    -- the dual of `G` has the cardinality of `G`, by Mathlib's character duality
    have hcard : Fintype.card (G →* Mˣ) = Nat.card G := by
      simpa using card_monoidHom_of_hasEnoughRootsOfUnity G M
    simp [hcard]
  · next hg => exact sum_monoidHom_apply_eq_zero_of_ne_one hg

/-- **Tagged column orthogonality.** Summing `(χ σ)⁻¹ * χ g` over all characters isolates the
single element `σ`: the sum is `Nat.card G` when `g = σ` and `0` otherwise. This is the form a
fibre-selecting argument uses, `sum_monoidHom_apply_eq_ite` being the case `σ = 1`.

The inverse sits on the tag `σ`, not on the argument `g`. Without it the sum is
`∑ χ, χ (σ * g)`, which is the indicator of `g = σ⁻¹` — a different fibre, and one that genuinely
differs whenever `σ` is not an involution. -/
@[simp]
theorem sum_inv_mul_monoidHom_apply_eq_ite [DecidableEq G] (σ g : G) :
    ∑ χ : G →* Mˣ, (((χ σ)⁻¹ : Mˣ) : M) * ((χ g : Mˣ) : M) =
      if g = σ then (Nat.card G : M) else 0 := by
  have key : ∀ χ : G →* Mˣ, (((χ σ)⁻¹ : Mˣ) : M) * ((χ g : Mˣ) : M) = ((χ (σ⁻¹ * g) : Mˣ) : M) :=
    fun χ ↦ by rw [map_mul, map_inv, Units.val_mul]
  simp only [key, sum_monoidHom_apply_eq_ite, inv_mul_eq_one, eq_comm]

end CommGroup

namespace TauCeti

variable [Group G]

/-- **The character sum at an element of the commutator subgroup counts the characters.** Every
character `χ : G →* Mˣ` kills the commutator subgroup, so at such an element every summand of the
column sum is `1`. For a commutative group the commutator subgroup is trivial and this is the
`g = 1` case of `CommGroup.sum_monoidHom_apply_eq_ite`; for a non-commutative group it is the
value at which the column relation breaks. -/
@[simp]
theorem sum_monoidHom_apply_eq_card_of_mem_commutator {g : G} (hg : g ∈ commutator G) :
    ∑ χ : G →* Mˣ, (χ g : M) = Nat.card (G →* Mˣ) := by
  have h (χ : G →* Mˣ) : (χ g : M) = 1 := by
    rw [MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker χ hg), Units.val_one]
  simp [h, Nat.card_eq_fintype_card]

/-- **Column orthogonality fails for every finite non-commutative group.** In a non-commutative
group some commutator `g = ⁅a, b⁆` differs from `1`, and every character kills it, so the tagged
sum at `σ = 1` and this `g` is the number of characters rather than the `0` that
`CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` gives for `g ≠ σ` in a commutative group. Besides
the standing assumption that `M` is a domain, the only hypothesis on `M` is that this count is
nonzero in `M`; in characteristic zero it is supplied by `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`,
and no roots of unity are needed. -/
theorem exists_sum_inv_mul_monoidHom_apply_ne_ite [DecidableEq G] (hG : ¬ IsMulCommutative G)
    (hcard : (Nat.card (G →* Mˣ) : M) ≠ 0) :
    ∃ σ g : G, ∑ χ : G →* Mˣ, (((χ σ)⁻¹ : Mˣ) : M) * ((χ g : Mˣ) : M) ≠
      if g = σ then (Nat.card G : M) else 0 := by
  obtain ⟨a, b, hab⟩ : ∃ a b : G, ⁅a, b⁆ ≠ 1 := by
    contrapose! hG
    exact IsMulCommutative.of_comm fun a b ↦ commutatorElement_eq_one_iff_mul_comm.mp (hG a b)
  refine ⟨1, ⁅a, b⁆, ?_⟩
  rw [ite_eq_right hab]
  simp only [map_one, inv_one, Units.val_one, one_mul]
  rw [sum_monoidHom_apply_eq_card_of_mem_commutator
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))]
  exact hcard

end TauCeti
