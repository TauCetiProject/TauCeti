/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Reduction
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Root

/-!
# Good primes for resolvents

Specializing an integral resolvent and reducing modulo a prime commute without hypotheses.
Interpreting that reduction as a subgroup test requires two separability conditions: the
original polynomial must retain distinct roots, and the resolvent must retain distinct orbit
values. These are the nondivisibility of their respective discriminants.

`TauCeti.ResolventSpec.IsGoodPrime` records both conditions. For a monic polynomial it is
equivalent to separability of the reduction and of its specialized resolvent. The reduced
resolvent then has a root in the prime field exactly when the Galois image of the reduced
polynomial lies in a conjugate of the specification's subgroup. This is a statement about
the Galois group over the prime field, with no assertion about the characteristic-zero
Galois group.

Renaming the invariant preserves the condition, just as it preserves the resolvent itself.
The degree of the resolvent is already preserved at every prime by
`ResolventSpec.natDegree_specialize`; goodness concerns separability alone.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, Springer 1993, §6.3.
-/

public section

open Polynomial

namespace TauCeti.ResolventSpec

variable {n : ℕ} (spec : ResolventSpec n) {f : ℤ[X]} {p : ℕ}

/-- A prime candidate is good for a polynomial and a resolvent specification when it divides
neither the polynomial discriminant nor the discriminant of the specialized resolvent.
Primality is supplied separately when interpreting reduction over a field. -/
def IsGoodPrime (f : ℤ[X]) (p : ℕ) : Prop :=
  TauCeti.IsGoodPrime f p ∧ TauCeti.IsGoodPrime (spec.specialize ℤ f) p

/-- The two discriminant conditions defining a good prime for a resolvent. -/
@[simp]
theorem isGoodPrime_iff (f : ℤ[X]) (p : ℕ) :
    spec.IsGoodPrime f p ↔
      ¬ (p : ℤ) ∣ f.discr ∧ ¬ (p : ℤ) ∣ (spec.specialize ℤ f).discr := by
  simp only [IsGoodPrime, TauCeti.isGoodPrime_iff]

/-- Construct joint goodness from goodness for the polynomial and for its resolvent. -/
theorem IsGoodPrime.mk (hf : TauCeti.IsGoodPrime f p)
    (hres : TauCeti.IsGoodPrime (spec.specialize ℤ f) p) : spec.IsGoodPrime f p :=
  ⟨hf, hres⟩

/-- Joint goodness implies goodness for the original polynomial. -/
theorem IsGoodPrime.polynomial {spec : ResolventSpec n} (h : spec.IsGoodPrime f p) :
    TauCeti.IsGoodPrime f p :=
  h.1

/-- Joint goodness implies goodness for the integral specialized resolvent. -/
theorem IsGoodPrime.resolvent {spec : ResolventSpec n} (h : spec.IsGoodPrime f p) :
    TauCeti.IsGoodPrime (spec.specialize ℤ f) p :=
  h.2

/-- A good prime for a resolvent preserves separability of the original monic polynomial. -/
theorem IsGoodPrime.separable_map {spec : ResolventSpec n} (h : spec.IsGoodPrime f p)
    (hf : f.Monic) [Fact p.Prime] :
    (f.map (Int.castRingHom (ZMod p))).Separable :=
  (hf.separable_map_zmod_iff_not_dvd_discr p).mpr
    ((TauCeti.isGoodPrime_iff f p).mp h.polynomial)

/-- A good prime for a resolvent preserves separability of the specialized resolvent.
No monicity or degree hypothesis on the original polynomial is needed for this implication. -/
theorem IsGoodPrime.separable_specialize {spec : ResolventSpec n}
    (h : spec.IsGoodPrime f p) [Fact p.Prime] :
    (spec.specialize (ZMod p) (f.map (Int.castRingHom (ZMod p)))).Separable := by
  rw [← spec.specialize_map]
  exact ((spec.monic_specialize ℤ f).separable_map_zmod_iff_not_dvd_discr p).mpr
    ((TauCeti.isGoodPrime_iff _ p).mp h.resolvent)

/-- For a monic polynomial, joint goodness is exactly separability of the reduction and of
the resolvent specialized at that reduction. -/
theorem isGoodPrime_iff_separable (hf : f.Monic) (p : ℕ) [Fact p.Prime] :
    spec.IsGoodPrime f p ↔
      (f.map (Int.castRingHom (ZMod p))).Separable ∧
        (spec.specialize (ZMod p) (f.map (Int.castRingHom (ZMod p)))).Separable := by
  rw [isGoodPrime_iff, ← spec.specialize_map,
    hf.separable_map_zmod_iff_not_dvd_discr,
    (spec.monic_specialize ℤ f).separable_map_zmod_iff_not_dvd_discr]

variable {E : Type*} [Field E] [Algebra (ZMod p) E] [Fact p.Prime]
  [IsGalois (ZMod p) E]
  [Fact ((f.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) E)).Splits]

/-- At a jointly good prime, a root of the reduced integral resolvent detects containment
of the Galois image of the reduced polynomial in a conjugate of the specification's subgroup.
The root numbering is explicit, and `E` may be any Galois splitting extension. -/
theorem IsGoodPrime.exists_isRoot_map_specialize_iff {spec : ResolventSpec n}
    (h : spec.IsGoodPrime f p) (hf : f.Monic) (hdeg : f.natDegree = n)
    (e : (f.map (Int.castRingHom (ZMod p))).rootSet E ≃ Fin n) :
    (∃ a : ZMod p, ((spec.specialize ℤ f).map (Int.castRingHom (ZMod p))).IsRoot a) ↔
      ∃ τ : Equiv.Perm (Fin n),
        (Gal.galActionHom (f.map (Int.castRingHom (ZMod p))) E).range.map
          (e.permCongrHom : _ →* Equiv.Perm (Fin n)) ≤
            spec.H.map (MulAut.conj τ).toMonoidHom := by
  rw [spec.specialize_map]
  exact spec.exists_isRoot_specialize_iff_exists_le_map_conj (hf.map _) (h.separable_map hf)
    ((hf.natDegree_map _).trans hdeg) e h.separable_specialize

end TauCeti.ResolventSpec
