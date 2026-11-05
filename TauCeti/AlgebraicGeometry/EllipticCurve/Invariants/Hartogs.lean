/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Invariants.CuspidalLocus
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Hartogs

/-!
# Sections on the smooth-or-nodal Weierstrass atlas

Let `A = ℤ[a₁,a₂,a₃,a₄,a₆]`. The open `D(c₄) ∪ D(Δ)` of `Spec A` retains the nodal
cubics and removes the cuspidal locus. Every section of its structure sheaf extends uniquely
to a coefficient polynomial. The same restriction is an isomorphism on global sections after
any flat base change of the atlas. This is the atlas-level Hartogs comparison used to pass
from regular sections to polynomial invariants; it does not construct a quotient stack or
descent of the Hodge line.

The geometric extension uses the algebraic Hartogs theorem in
`TauCeti.AlgebraicGeometry.Modules.Tilde.Hartogs` and the relatively prime invariants in
`TauCeti.AlgebraicGeometry.EllipticCurve.Invariants.CuspidalLocus`.

## References

* P. Goerss, *Topological modular forms [after Hopkins, Miller, and Lurie]*, §3.1.
* T. Bauer, *Computation of the homotopy of the spectrum tmf*, §3.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry
open RingTheory.Sequence MvPolynomial

namespace WeierstrassCurve.Universal

/-- The smooth-or-nodal open of the universal cubic atlas: the complement of `V(c₄, Δ)`. -/
noncomputable def compactifiedOpen : (Spec (.of (MvPolynomial Coeff ℤ))).Opens :=
  PrimeSpectrum.basicOpen curve.c₄ ⊔ PrimeSpectrum.basicOpen curve.Δ

@[simp]
theorem mem_compactifiedOpen (p : PrimeSpectrum (MvPolynomial Coeff ℤ)) :
    p ∈ compactifiedOpen ↔ curve.c₄ ∉ p.asIdeal ∨ curve.Δ ∉ p.asIdeal :=
  Iff.rfl

/-- The two invariants defining the removed cusp form a weakly regular sequence over `ℤ`. -/
theorem isWeaklyRegular_c₄_Δ :
    IsWeaklyRegular (MvPolynomial Coeff ℤ) [curve.c₄, curve.Δ] := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  refine ⟨IsSMulRegular.of_ne_zero irreducible_c₄.ne_zero, ?_⟩
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro x hx
  -- Membership in `c₄ • ⊤` is divisibility by `c₄`; coprimality cancels `Δ`.
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  have hdiv : curve.c₄ ∣ curve.Δ * x := ⟨y, hy.symm⟩
  obtain ⟨z, hz⟩ := isRelPrime_c₄_Δ.dvd_of_dvd_mul_left hdiv
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨z, trivial, hz.symm⟩

/-- **Hartogs extension on the cubic atlas.** Restricting coefficient polynomials to
`D(c₄) ∪ D(Δ)` is bijective, so every regular function there is a unique polynomial. -/
theorem algebraMap_compactifiedOpen_bijective :
    Function.Bijective
      (algebraMap (MvPolynomial Coeff ℤ)
        ((Spec.structureSheaf (MvPolynomial Coeff ℤ)).presheaf.obj (op compactifiedOpen))) := by
  -- For the ring as a module over itself, Mathlib's `toOpenₗ` is this algebra map.
  exact TauCeti.AlgebraicGeometry.StructureSheaf.toOpenₗ_bijective_of_isWeaklyRegular
    isWeaklyRegular_c₄_Δ le_sup_left le_sup_right

/-- Restriction to the smooth-or-nodal atlas remains an isomorphism on global sections after
any flat base change. In particular it applies to polynomial and localized coordinate charts
of the change-of-variables group. -/
theorem isIso_appTop_pullback_compactifiedOpen (B : Type) [CommRing B]
    [Algebra (MvPolynomial Coeff ℤ) B] [Module.Flat (MvPolynomial Coeff ℤ) B] :
    IsIso (Limits.pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial Coeff ℤ) B)))
      compactifiedOpen.ι).appTop :=
  TauCeti.AlgebraicGeometry.isIso_appTop_pullback_fst_ι_of_isWeaklyRegular
    B compactifiedOpen isWeaklyRegular_c₄_Δ le_sup_left le_sup_right

end WeierstrassCurve.Universal
