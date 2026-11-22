/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertModular.PolarizationLattice
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.RowStabilizer

/-!
# The finite adelic stabilizer of a polarization lattice

For `J = c⁻¹𝔡⁻¹`, the finite adelic row lattice is `Ô ⊕ JÔ`. Its endomorphism order
consists of matrices with entries in `[[Ô, JÔ], [J⁻¹Ô, Ô]]`. The subgroup
`adelicPolarizationStabilizer c` consists of the matrices in this order whose determinant
is an everywhere integral unit. The diagonal rational points of the row lattice recover
`polarizationLattice c`. These constructions include nonprincipal polarization ideals.

## References

* C. Birkbeck, B. Heuer and C. Williams, *Overconvergent Hilbert modular forms via perfectoid
  modular varieties*, Ann. Inst. Fourier 73 (2023), Notation 5.1(3) and Definition 5.2(1).
-/

public section

open NumberField FractionalIdeal IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped nonZeroDivisors

namespace TauCeti.HilbertModular

variable {K : Type*} [Field K] [NumberField K]

/-- The finite adelic row stabilizer of the Hilbert polarization lattice with ideal `c`. -/
noncomputable abbrev adelicPolarizationStabilizer (c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) 𝔸ᶠ[𝓞 K, K]) :=
  finiteAdelicRowStabilizer (polarizationCoordinateIdeal c)

/-- The rational points of the finite adelic row lattice are exactly the original polarization
lattice. -/
theorem algebraMap_mem_finiteAdelicRowLattice_polarizationCoordinateIdeal_iff
    (c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Fin 2 → K) :
    (fun i ↦ algebraMap K 𝔸ᶠ[𝓞 K, K] (x i)) ∈
        finiteAdelicRowLattice (polarizationCoordinateIdeal c) ↔
      x ∈ polarizationLattice (c : FractionalIdeal (𝓞 K)⁰ K) := by
  simp only [mem_finiteAdelicRowLattice, algebraMap_mem_finiteAdelicIdeal_iff,
    mem_polarizationLattice, coe_polarizationCoordinateIdeal, algebraMap_mem_integralAdeles_iff,
    mem_one_iff, RingHom.mem_range]

end TauCeti.HilbertModular
