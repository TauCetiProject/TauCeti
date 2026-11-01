/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.OrbifoldDefect
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.FiniteHolomorphicMap
public import TauCeti.Analysis.Complex.RiemannSurface.Ramification
public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Cofinite
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Finite
import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Cofinite

/-!
# Total ramification in terms of cusp counts and elliptic orders

For a finite-index inclusion `Δ ≤ Γ` of cofinite Fuchsian groups, let `d = [Γ : Δ]`, let
`s` denote a group's number of cusp orbits, and let `a = ∑ (1 - 1/m)` over its elliptic
orbits, with effective stabilizer orders `m`. The compactified quotient map satisfies

`ramificationDegree + s_Δ + a_Δ = d * (s_Γ + a_Γ)`.

This is the ramification calculation needed to turn the ordinary Riemann–Hurwitz formula
for the compactified surfaces into multiplicativity of the orbifold Euler characteristic.
It does not define genus or assume a genus formula. Cofiniteness supplies compactness and
finiteness of the elliptic and cusp sets by the existing Dirichlet polygon theorems.

The proof sums the local complementary-defect identity and regroups by fibres, whose sums
of local multiplicities are the subgroup index.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §3.1.
* Svetlana Katok, *Fuchsian Groups*, §4.3.
-/

public noncomputable section

open Function MulAction Set TauCeti.RiemannSurface UpperHalfPlane
open Subgroup Subgroup.CompactifiedQuotient
open scoped MatrixGroups

namespace TauCeti.Fuchsian

variable {Δ Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Δ] [DiscreteTopology Γ]

/-- **The total ramification formula in orbifold defects.** Total ramification plus the
source's defects equals the subgroup index times the target's defects. -/
theorem ramificationDegree_add_finsum_orbifoldDefect (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ]
    (hΓ : Γ.IsCofinite) :
    (ramificationDegree (compactifiedQuotientMap h) : ℝ) +
        ∑ᶠ x : Δ.CompactifiedQuotient, orbifoldDefect x =
      (Δ.subgroupOf Γ).index * ∑ᶠ y : Γ.CompactifiedQuotient, orbifoldDefect y := by
  have hΔ : Δ.IsCofinite :=
    (isCofinite_iff_isCofinite_and_finiteIndex h).mpr ⟨hΓ, inferInstance⟩
  have := hΔ.compactSpace_compactifiedQuotient
  have := hΔ.finite_cuspOrbit
  have := hΓ.finite_cuspOrbit
  have hD := finite_support_orbifoldDefect (Γ := Δ) hΔ.finite_ellipticOrbits
  let f := compactifiedQuotientFiniteHolomorphicMap h
  let w (x : Δ.CompactifiedQuotient) : ℝ :=
    (localMultiplicity (compactifiedQuotientMap h) x : ℝ) *
      orbifoldDefect (compactifiedQuotientMap h x)
  have hR : (support fun x : Δ.CompactifiedQuotient =>
      localMultiplicity (compactifiedQuotientMap h) x - 1).Finite := by
    refine f.finite_setOf_one_lt_localMultiplicity.subset ?_
    intro x hx
    simpa only [mem_support, Nat.sub_ne_zero_iff_lt,
      mem_ofPred_eq, f, coe_compactifiedQuotientFiniteHolomorphicMap] using hx
  have hRcast : (support fun x : Δ.CompactifiedQuotient =>
      ((localMultiplicity (compactifiedQuotientMap h) x - 1 : ℕ) : ℝ)).Finite :=
    hR.subset fun x hx => Nat.cast_ne_zero.mp hx
  have hpoint (x : Δ.CompactifiedQuotient) :
      ((localMultiplicity (compactifiedQuotientMap h) x - 1 : ℕ) : ℝ) + orbifoldDefect x = w x := by
    have hpos := localMultiplicity_pos f x
    simp only [f, coe_compactifiedQuotientFiniteHolomorphicMap] at hpos
    rw [Nat.cast_sub hpos, Nat.cast_one]
    have hid := localMultiplicity_mul_one_sub_orbifoldDefect h x
    dsimp only [w]
    linarith
  have hsum : (ramificationDegree (compactifiedQuotientMap h) : ℝ) +
      ∑ᶠ x : Δ.CompactifiedQuotient, orbifoldDefect x = ∑ᶠ x, w x := by
    have hcast := map_finsum (Nat.castAddMonoidHom ℝ) hR
    simp only [Nat.coe_castAddMonoidHom] at hcast
    rw [ramificationDegree_def, hcast,
      ← finsum_add_distrib (by simpa only [HasFiniteSupport] using hRcast)
        (by simpa only [HasFiniteSupport] using hD)]
    exact finsum_congr hpoint
  rw [hsum]
  exact finsum_localMultiplicity_mul_orbifoldDefect h hΓ.finite_ellipticOrbits

/-- **Total ramification through cusp counts and elliptic orders.** For a finite-index inclusion
of cofinite groups, `R + s_Δ + ∑(1 - 1/m_Δ) = [Γ : Δ] * (s_Γ + ∑(1 - 1/m_Γ))`, where `R`
is the ramification degree of the induced map of compactified surfaces. -/
theorem ramificationDegree_eq_orbifold_defect (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ]
    (hΓ : Γ.IsCofinite) :
    (ramificationDegree (compactifiedQuotientMap h) : ℝ) =
      (Δ.subgroupOf Γ).index * ((Nat.card Γ.CuspOrbit : ℝ) +
        ∑ᶠ q ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹)) -
      ((Nat.card Δ.CuspOrbit : ℝ) +
        ∑ᶠ q ∈ Δ.ellipticOrbits, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹)) := by
  have hΔ : Δ.IsCofinite :=
    (isCofinite_iff_isCofinite_and_finiteIndex h).mpr ⟨hΓ, inferInstance⟩
  have := hΔ.finite_cuspOrbit
  have := hΓ.finite_cuspOrbit
  have hsum := ramificationDegree_add_finsum_orbifoldDefect h hΓ
  rw [finsum_orbifoldDefect hΔ.finite_ellipticOrbits,
    finsum_orbifoldDefect hΓ.finite_ellipticOrbits] at hsum
  linarith

end TauCeti.Fuchsian
