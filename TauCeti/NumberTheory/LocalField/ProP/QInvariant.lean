/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ProP.Demushkin
public import TauCeti.NumberTheory.LocalField.RootsOfUnity.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.QInvariant
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Prescription
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Character.Image

/-!
# The `q`-invariant of the Demushkin group `G_K(p)`

Let `K` be a nonarchimedean local field containing a primitive `p`th root of unity, so that the
maximal pro-`p` quotient `G_K(p)` of its absolute Galois group is a Demushkin group
(`TauCeti.isDemushkin_absoluteGaloisGroupProP_of_mu`). Labute's `q`-invariant of `G_K(p)`, the
order of the torsion subgroup of its topological abelianization (`TauCeti.demushkinQ`), is the
number `q(K)` of `p`-power roots of unity in `K` (`TauCeti.localRootOfUnityOrder`).

This is the value of `q` substituted into Labute's marked classification of Demushkin groups when it
is applied to `G_K(p)`, alongside the rank `[K : ℚ_p] + 2`
(`TauCeti.demushkinRank_absoluteGaloisGroupProP`).

## Main results

* `TauCeti.demushkinQ_absoluteGaloisGroupProP`: `q(G_K(p)) = q(K)`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132,
  Theorem 4 and its corollary.
* J.-P. Serre, *Structure de certains pro-p-groupes*, Séminaire Bourbaki 252 (1962/63).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.5.11).
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The `q`-invariant of `G_K(p)` is the number of `p`-power roots of unity of `K`.** For a
nonarchimedean local field `K` containing a primitive `p`th root of unity, Labute's `q`-invariant
of the Demushkin group `G_K(p)` is `q(K)`, the order of the group of `p`-power roots of unity
of `K`. -/
theorem demushkinQ_absoluteGaloisGroupProP (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (h : Finite (pPowerRootsOfUnity p K)) :
    demushkinQ (isDemushkin_absoluteGaloisGroupProP_of_mu p K hmu) =
      localRootOfUnityOrder p K h := by
  set hG := isDemushkin_absoluteGaloisGroupProP_of_mu p K hmu
  have : NeZero (p : K) := hmu.choose_spec.neZero'
  -- The cyclotomic orientation has the prescription property, so it is the canonical character.
  -- The canonical character lands in `1 + p^kℤ_p` exactly when `p^k ∣ q(G_K(p))`, and the
  -- cyclotomic character lands there exactly when `K` contains a primitive `p^k`th root of
  -- unity, that is when `p^k ∣ q(K)`. So both invariants are divisible by the same powers of `p`.
  have hχ := (cyclotomicOrientation_hasPrescriptionProperty p K hmu).eq_demushkinCharacter hG
  have hdvd (k : ℕ) : p ^ k ∣ demushkinQ hG ↔ p ^ k ∣ localRootOfUnityOrder p K h := by
    rw [← range_demushkinCharacter_le_unitsPrincipal_iff hG, ← hχ, cyclotomicOrientation_range,
      range_localCyclotomicCharacter_le_unitsPrincipal_iff,
      primitiveRoot_pow_iff_dvd_localRootOfUnityOrder_of_finite]
  -- Both invariants are powers of `p`. `q(K) = p^n` is positive, so `p^(n+1)` does not divide
  -- it, and hence `q(G_K(p)) ≠ 0`; comparing exponents then gives equality.
  obtain ⟨n, hn⟩ := localRootOfUnityOrder_isPow p K h
  have h0 : demushkinQ hG ≠ 0 := fun h0 ↦ by
    have hle := (hdvd (n + 1)).1 (h0 ▸ dvd_zero _)
    rw [hn, Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt] at hle
    omega
  obtain ⟨m, -, hm⟩ := hG.exists_demushkinQ_eq_pow h0
  rw [hm, hn] at hdvd ⊢
  exact Nat.dvd_antisymm ((hdvd m).1 dvd_rfl) ((hdvd n).2 dvd_rfl)

end TauCeti
