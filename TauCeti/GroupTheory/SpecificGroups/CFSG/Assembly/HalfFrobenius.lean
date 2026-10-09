/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType

/-!
# The half-Frobenius of every Suzuki--Ree index

Each of the four half-Frobenius families carries an exceptional isogeny `τ` of its ambient group:
the special isogeny of the rank-two symplectic carrier for the Suzuki groups, of the short-root
`G₂` carrier over `𝔽₃` for the Ree groups of type `G₂`, and of the short-root `F₄` carrier over
`𝔽₂` for the Ree groups of type `F₄` and the Tits group. This file selects that isogeny for an
arbitrary `TauCeti.SuzukiReeIndex`, as an endomorphism of the uniform ambient group
`TauCeti.ValidLieTypeIndex.AmbientGroup`, and states its defining equations once for all four
families:

```text
τ (x_i(t)) = x_{σ i}(t ^ e_i),      τ ∘ τ = Frob_p,      steinberg = τ ^ (2m + 1),
```

where `σ` is `TauCeti.SuzukiReeIndex.lengthPerm`, `e_i` is `TauCeti.SuzukiReeIndex.exponent`
(`1` on a long simple root and `p` on a short one), `Frob_p` is the prime-field Frobenius
`TauCeti.ValidLieTypeIndex.primeFrobenius`, and `2m + 1` is the field exponent the index records.
The first equation is what identifies the selected isogeny: the opposite assignment of exponents
would also square to `Frob_p`. The last says that the uniform Steinberg endomorphism
`TauCeti.ValidLieTypeIndex.steinberg` of a half-Frobenius family is the odd power of this map,
and not `τ ∘ Frob_q`.

As with the ambient group, nothing here identifies `τ` with the special isogeny of a pinned
simply connected group scheme; that comparison transfers along an identification of the carriers.

## Main definitions

* `TauCeti.SuzukiReeIndex.halfFrobenius`: the exceptional isogeny of the ambient group of a
  Suzuki--Ree index, with branch equations `TauCeti.SuzukiReeIndex.halfFrobenius_suzuki`,
  `TauCeti.SuzukiReeIndex.halfFrobenius_reeG2`, `TauCeti.SuzukiReeIndex.halfFrobenius_reeF4` and
  `TauCeti.SuzukiReeIndex.halfFrobenius_tits`.

## Main results

* `TauCeti.SuzukiReeIndex.halfFrobenius_simpleRootSubgroup`: the action on the Bourbaki-numbered
  simple root subgroups, through the length permutation and exponents of the index.
* `TauCeti.SuzukiReeIndex.halfFrobenius_halfFrobenius` and
  `TauCeti.SuzukiReeIndex.halfFrobenius_sq`: the square of the half-Frobenius is
  the prime-field Frobenius.
* `TauCeti.SuzukiReeIndex.steinberg_eq_halfFrobenius_pow`: the Steinberg endomorphism is the
  `(2m + 1)`-st power of the half-Frobenius.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
-/

public section

namespace TauCeti

namespace SuzukiReeIndex

open LieTypeIndex (usesHalfFrobenius_iff)

noncomputable section

/-- **The half-Frobenius of a Suzuki--Ree index**: the exceptional isogeny of the carrier of its
family, as an endomorphism of the uniform ambient group. On each of the four families it is the
family's special isogeny, by `halfFrobenius_suzuki` and its siblings; its action on the simple
root subgroups is `halfFrobenius_simpleRootSubgroup`, and its square is the prime-field Frobenius
by `halfFrobenius_halfFrobenius`. -/
def halfFrobenius : (e : SuzukiReeIndex) → e.1.AmbientGroup →* e.1.AmbientGroup
  | ⟨⟨.A _ _, _⟩, h⟩ | ⟨⟨.twistedA _ _, _⟩, h⟩ | ⟨⟨.B _ _, _⟩, h⟩ | ⟨⟨.C _ _, _⟩, h⟩
  | ⟨⟨.D _ _, _⟩, h⟩ | ⟨⟨.twistedD _ _, _⟩, h⟩ | ⟨⟨.E6 _, _⟩, h⟩ | ⟨⟨.E7 _, _⟩, h⟩
  | ⟨⟨.E8 _, _⟩, h⟩ | ⟨⟨.F4 _, _⟩, h⟩ | ⟨⟨.G2 _, _⟩, h⟩ | ⟨⟨.twistedE6 _, _⟩, h⟩
  | ⟨⟨.trialityD4 _, _⟩, h⟩ => absurd h (by simp [usesHalfFrobenius_iff])
  | ⟨⟨.suzuki _, hv⟩, _⟩ => SuzukiLieIndex.halfFrobenius ⟨⟨_, hv⟩, by simp⟩
  | ⟨⟨.reeG2 m, hv⟩, _⟩ => (ReeG2LieIndex.of m hv).halfFrobenius
  | ⟨⟨.reeF4 m, hv⟩, _⟩ => (ReeF4LieIndex.of m hv).halfFrobenius
  | ⟨⟨.tits, _⟩, _⟩ => TitsLieIndex.of.steinberg

/-! ### The branch equations -/

section Branches

variable {m : ℕ}

/-- On `²B₂(2^(2m+1))` the half-Frobenius is that of the Suzuki family, the special isogeny of
the rank-two symplectic carrier. -/
theorem halfFrobenius_suzuki (hv : (LieTypeIndex.suzuki m).Valid) :
    halfFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      SuzukiLieIndex.halfFrobenius ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On `²G₂(3^(2m+1))` the half-Frobenius is that of the Ree `G₂` family. -/
theorem halfFrobenius_reeG2 (hv : (LieTypeIndex.reeG2 m).Valid) :
    halfFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      (ReeG2LieIndex.of m hv).halfFrobenius :=
  (rfl)

/-- On `²F₄(2^(2m+1))` the half-Frobenius is that of the Ree `F₄` family. -/
theorem halfFrobenius_reeF4 (hv : (LieTypeIndex.reeF4 m).Valid) :
    halfFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      (ReeF4LieIndex.of m hv).halfFrobenius :=
  (rfl)

/-- On the Tits index the half-Frobenius is the Tits Steinberg endomorphism, which is the special
isogeny of the short-root `F₄` carrier over `𝔽₂` by `TauCeti.TitsLieIndex.steinberg_def`: the Tits
index records field exponent one, so its Steinberg endomorphism is the half-Frobenius itself. -/
theorem halfFrobenius_tits (hv : LieTypeIndex.tits.Valid) :
    halfFrobenius ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = TitsLieIndex.of.steinberg :=
  (rfl)

end Branches

/-! ### The defining equations -/

/-- **The half-Frobenius has the pinned action on every simple root subgroup.** It sends
`x_i(u)` to `x_{σ i}(u ^ e_i)`, for `σ` the length permutation of the index and `e_i` its
exponent, `1` on a long simple root and the defining characteristic on a short one. -/
@[simp]
theorem halfFrobenius_simpleRootSubgroup (e : SuzukiReeIndex) (i : Fin e.1.rank)
    (u : Multiplicative e.1.Closure) :
    e.halfFrobenius (e.1.simpleRootSubgroup i u) =
      e.1.simpleRootSubgroup (e.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ e.exponent i)) := by
  -- On each family the branch equations turn the uniform maps into the family's own, whose
  -- action formula closes the goal.
  obtain ⟨⟨d, hv⟩, h⟩ := e
  cases d
  all_goals try { simp [usesHalfFrobenius_iff] at h }
  · rw [halfFrobenius_suzuki, ValidLieTypeIndex.simpleRootSubgroup_suzuki]
    exact SuzukiLieIndex.halfFrobenius_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [halfFrobenius_reeG2, ValidLieTypeIndex.simpleRootSubgroup_reeG2]
    exact ReeG2LieIndex.halfFrobenius_simpleRootSubgroup (ReeG2LieIndex.of _ hv) i u
  · rw [halfFrobenius_reeF4, ValidLieTypeIndex.simpleRootSubgroup_reeF4]
    exact ReeF4LieIndex.halfFrobenius_simpleRootSubgroup (ReeF4LieIndex.of _ hv) i u
  · rw [halfFrobenius_tits, ValidLieTypeIndex.simpleRootSubgroup_tits]
    exact TitsLieIndex.steinberg_simpleRootSubgroup TitsLieIndex.of i u

/-- **The square of the half-Frobenius is the prime-field Frobenius**, `τ (τ g) = Frob_p g` for
`p` the defining characteristic of the index. -/
@[simp]
theorem halfFrobenius_halfFrobenius (e : SuzukiReeIndex) (g : e.1.AmbientGroup) :
    e.halfFrobenius (e.halfFrobenius g) = e.1.primeFrobenius g := by
  obtain ⟨⟨d, hv⟩, h⟩ := e
  cases d
  all_goals try { simp [usesHalfFrobenius_iff] at h }
  · rw [halfFrobenius_suzuki, ValidLieTypeIndex.primeFrobenius_suzuki]
    exact SuzukiLieIndex.halfFrobenius_halfFrobenius ⟨⟨_, hv⟩, by simp⟩ g
  · rw [halfFrobenius_reeG2, ValidLieTypeIndex.primeFrobenius_reeG2]
    exact ReeG2LieIndex.halfFrobenius_halfFrobenius (ReeG2LieIndex.of _ hv) g
  · rw [halfFrobenius_reeF4, ValidLieTypeIndex.primeFrobenius_reeF4]
    exact ReeF4LieIndex.halfFrobenius_halfFrobenius (ReeF4LieIndex.of _ hv) g
  · rw [halfFrobenius_tits, ValidLieTypeIndex.primeFrobenius_tits]
    exact TitsLieIndex.steinberg_steinberg TitsLieIndex.of g

/-- The square relation `τ ^ 2 = Frob_p` as an equation in the endomorphism monoid. -/
theorem halfFrobenius_sq (e : SuzukiReeIndex) :
    HPow.hPow (α := Monoid.End e.1.AmbientGroup) e.halfFrobenius 2 = e.1.primeFrobenius :=
  (pow_two (M := Monoid.End _) _).trans (MonoidHom.ext e.halfFrobenius_halfFrobenius)

/-- **The Steinberg endomorphism of a Suzuki--Ree index is the odd power `τ ^ (2m + 1)` of its
half-Frobenius**, for `2m + 1` the field exponent the index records. -/
theorem steinberg_eq_halfFrobenius_pow (e : SuzukiReeIndex) :
    e.1.steinberg =
      HPow.hPow (α := Monoid.End e.1.AmbientGroup) e.halfFrobenius e.1.fieldExponent := by
  obtain ⟨⟨d, hv⟩, h⟩ := e
  cases d
  all_goals try { simp [usesHalfFrobenius_iff] at h }
  · rw [ValidLieTypeIndex.steinberg_suzuki, halfFrobenius_suzuki]
    exact SuzukiLieIndex.steinberg_def ⟨⟨_, hv⟩, by simp⟩
  · rw [ValidLieTypeIndex.steinberg_reeG2, halfFrobenius_reeG2]
    exact ReeG2LieIndex.steinberg_def (ReeG2LieIndex.of _ hv)
  · rw [ValidLieTypeIndex.steinberg_reeF4, halfFrobenius_reeF4]
    exact ReeF4LieIndex.steinberg_def (ReeF4LieIndex.of _ hv)
  · rw [ValidLieTypeIndex.steinberg_tits, halfFrobenius_tits]
    simp only [ValidLieTypeIndex.fieldExponent, LieTypeIndex.fieldExponent_tits]
    exact (pow_one (M := Monoid.End _) _).symm

end

end SuzukiReeIndex

end TauCeti
