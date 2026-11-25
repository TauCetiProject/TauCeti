/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Support
public import TauCeti.AlgebraicGeometry.Modules.Unit
public import TauCeti.Examples.Algebra.Homology.LocalCohomology.DegreeZero

/-!
# Example: geometric and native `H⁰` differ on a non-Noetherian ring

Let `k` be a nonzero commutative ring, `A = k[x₀, x₁, …] ⧸ (x_j ^ (j + 2))` and
`I = (x₀, x₁, …)` (`TauCeti.LocalCohomologyDegreeZeroExample.TruncatedRing`, `ideal`). Every `x_j`
is nilpotent, so `V(I) = Spec A`, and the geometric degree-zero cohomology with supports in `V(I)`
is `H⁰_{V(I)}(Spec A, 𝒪) = Γ(Spec A, 𝒪) = A ≠ 0`
(`Scheme.Modules.cohomologyWithSupportZeroLinearEquivOfEqUniv`). The native local cohomology
`H⁰_I(A)`, the `I`-power torsion of `A`, vanishes
(`TauCeti.LocalCohomologyDegreeZeroExample.isZero_localCohomology_zero`), and `A` is not
Noetherian (`TauCeti.LocalCohomologyDegreeZeroExample.not_isNoetherianRing`), so the geometric and
native degree-zero groups cannot be identified without a hypothesis such as Noetherianity.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.LocalCohomologyDegreeZeroExample

namespace TauCeti.AlgebraicGeometry.SupportWholeSpectrumExample

universe u

variable (k : Type u) [CommRing k]

/-- The zero locus `V(I) = Spec A` of `I = (x₀, x₁, …)` in `Spec A`, as a closed subset. -/
noncomputable abbrev zeroLocusIdeal : Closeds (Spec (.of (TruncatedRing k))) :=
  ⟨PrimeSpectrum.zeroLocus (ideal k : Set (TruncatedRing k)), PrimeSpectrum.isClosed_zeroLocus _⟩

/-- **Geometric `H⁰_{V(I)}(Spec A, 𝒪) = A`.** Since `V(I)` is all of `Spec A`, the degree-zero
cohomology of the structure sheaf with supports in `V(I)` is the ring `A` of global functions. -/
noncomputable def cohomologyWithSupportZeroAddEquiv :
    (Scheme.Modules.unit (Spec (.of (TruncatedRing k)))).cohomologyWithSupport
      (zeroLocusIdeal k) ⊤ 0 ≃+ TruncatedRing k :=
  ((Scheme.Modules.unit _).cohomologyWithSupportZeroLinearEquivOfEqUniv _
    (zeroLocus_ideal (k := k))).toAddEquiv.trans
    (Scheme.ΓSpecIso (.of (TruncatedRing k))).commRingCatIsoToRingEquiv.toAddEquiv

@[simp]
lemma cohomologyWithSupportZeroAddEquiv_apply
    (x : (Scheme.Modules.unit (Spec (.of (TruncatedRing k)))).cohomologyWithSupport
      (zeroLocusIdeal k) ⊤ 0) :
    cohomologyWithSupportZeroAddEquiv k x =
      (Scheme.ΓSpecIso (.of (TruncatedRing k))).commRingCatIsoToRingEquiv
        ((Scheme.Modules.unit _).cohomologyWithSupportZeroLinearEquivOfEqUniv _
          (zeroLocus_ideal (k := k)) x) :=
  (rfl)

/-- **Geometric `H⁰_{V(I)}(Spec A, 𝒪) ≠ 0`** for a nonzero ring `k`, whereas the native `H⁰_I(A)`
vanishes (`isZero_localCohomology_zero`). -/
theorem nontrivial_cohomologyWithSupport_zero [Nontrivial k] :
    Nontrivial ((Scheme.Modules.unit (Spec (.of (TruncatedRing k)))).cohomologyWithSupport
      (zeroLocusIdeal k) ⊤ 0) := by
  have : Nontrivial (TruncatedRing k) :=
    Ideal.Quotient.nontrivial_iff.2 fun h ↦ one_notMem_relations (k := k) (h ▸ Submodule.mem_top)
  exact (cohomologyWithSupportZeroAddEquiv k).toEquiv.nontrivial

end TauCeti.AlgebraicGeometry.SupportWholeSpectrumExample
