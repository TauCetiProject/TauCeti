/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Map
public import TauCeti.RingTheory.Henselian.Radical

/-!
# Henselization depends only on the radical

Ideals with the same radical have canonically isomorphic henselizations as algebras over the
base ring. The equivalence `TauCeti.Henselization.algEquivOfRadicalEq` is characterized by the
universal lift into the henselian pair defined by the radical of the extended ideal. It is
compatible with reversal and composition of comparisons, and agrees with the existing map of
henselizations whenever the ideals are nested. Thus changing the ideal defining a closed subset
does not change its henselian neighbourhood.

The construction follows the universal-property argument of Stacks, Lemma 15.12.6, using
`TauCeti.Henselization.lift` and `algHom_ext_of_map_le_jacobson`.

## References

* [Stacks Project, Lemma 15.12.6](https://stacks.math.columbia.edu/tag/0F0L).
-/

public section

namespace TauCeti.Henselization

variable {R : Type*} [CommRing R] {I J K : Ideal R}

private theorem map_le_radical_extended (h : I.radical ≤ J.radical) :
    I.map (algebraMap R (algebra J)) ≤ (extended J).radical :=
  (Ideal.map_mono (Ideal.le_radical.trans h)).trans (Ideal.map_radical_le _)

/-- Ideals with the same radical have canonically isomorphic henselizations over the base ring.
Stacks, Lemma 15.12.6 (0F0L). -/
@[stacks 0F0L]
noncomputable def algEquivOfRadicalEq (h : I.radical = J.radical) :
    algebra I ≃ₐ[R] algebra J :=
  AlgEquiv.ofAlgHom
    (lift (map_le_radical_extended h.le))
    (lift (map_le_radical_extended h.ge))
    (algHom_ext_of_map_le_jacobson (extended_le_jacobson J))
    (algHom_ext_of_map_le_jacobson (extended_le_jacobson I))

/-- The radical comparison is the universal lift to the radical of the target's extended ideal.
This formula also characterizes its value on elements without unfolding the equivalence. -/
theorem algEquivOfRadicalEq_toAlgHom (h : I.radical = J.radical) :
    (algEquivOfRadicalEq h).toAlgHom =
      lift (J := (extended J).radical)
        ((Ideal.map_mono (Ideal.le_radical.trans h.le)).trans (Ideal.map_radical_le _)) := by
  exact algHom_ext_of_map_le_jacobson
    ((map_le_radical_extended h.le).trans HenselianRing.jac)

/-- Reversing the radical comparison gives the inverse algebra equivalence. -/
theorem algEquivOfRadicalEq_symm (h : I.radical = J.radical) :
    (algEquivOfRadicalEq h).symm = algEquivOfRadicalEq h.symm := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact algHom_ext_of_map_le_jacobson
    ((map_le_radical_extended h.ge).trans HenselianRing.jac)

/-- The comparison of an ideal with itself is the identity. -/
@[simp]
theorem algEquivOfRadicalEq_refl :
    algEquivOfRadicalEq (I := I) rfl = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact algHom_ext_of_map_le_jacobson (extended_le_jacobson I)

/-- Composing radical comparisons gives the comparison for the composite equality. -/
@[simp]
theorem algEquivOfRadicalEq_trans (hIJ : I.radical = J.radical)
    (hJK : J.radical = K.radical) :
    (algEquivOfRadicalEq hIJ).trans (algEquivOfRadicalEq hJK) =
      algEquivOfRadicalEq (hIJ.trans hJK) := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact algHom_ext_of_map_le_jacobson
    ((map_le_radical_extended (hIJ.trans hJK).le).trans HenselianRing.jac)

/-- When the ideals are nested, the radical comparison is the existing functorial map of
henselizations induced by the identity of the base ring. In particular, that map is bijective
when the ideals have the same radical. -/
theorem algEquivOfRadicalEq_toRingHom (h : I.radical = J.radical) (hIJ : I ≤ J) :
    (algEquivOfRadicalEq h).toRingHom = map (RingHom.id R) (by simpa using hIJ) := by
  apply map_unique
  ext r
  simp

-- Taking a positive power changes the defining ideal but preserves the henselization.
example (I : Ideal R) {n : ℕ} (hn : n ≠ 0) : Nonempty (algebra (I ^ n) ≃ₐ[R] algebra I) :=
  ⟨algEquivOfRadicalEq (I.radical_pow hn)⟩

-- A nilpotent defining ideal gives back the base ring, including in nonreduced rings.
example (I : Ideal R) (hI : IsNilpotent I) : Nonempty (algebra I ≃ₐ[R] R) := by
  obtain ⟨n, hn⟩ := hI
  have hrad : I.radical = (⊥ : Ideal R).radical := by
    by_cases hn0 : n = 0
    · have : Subsingleton (Ideal R) := by
        apply subsingleton_of_bot_eq_top
        simpa [hn0] using hn.symm
      exact Subsingleton.elim _ _
    · rw [← I.radical_pow hn0, ← Ideal.zero_eq_bot, hn]
  exact ⟨(algEquivOfRadicalEq hrad).trans (algEquivOfHenselianRing ⊥)⟩

end TauCeti.Henselization
