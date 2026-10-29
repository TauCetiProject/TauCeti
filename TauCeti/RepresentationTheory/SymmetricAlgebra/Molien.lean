/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
import TauCeti.LinearAlgebra.SymmetricAlgebra.Trace
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Reynolds

/-!
# Molien's formula

Let a finite group `G` act linearly on a finite-dimensional vector space `M` over a field `K` in
which `#G` is invertible. The invariant subalgebra `Sym(M)^G` is homogeneous, and its Hilbert
series records the dimensions of its homogeneous components:
`Hilb(Sym(M)^G, t) = ∑ₙ dim (Sym(M)^G ∩ Symⁿ M) tⁿ`.

On each homogeneous component `Symⁿ M` the Reynolds operator is the averaging projection of the
degree-`n` representation (`Representation.coe_averageMap_symmetricAlgebraHomogeneous`). A
projection has trace equal in `K` to the dimension of its image, and the trace of the average is
the average of the traces. Hence, in `K`,

`dim (Sym(M)^G ∩ Symⁿ M) = #G⁻¹ ∑_{g ∈ G} tr(g | Symⁿ M)`,

and summing over `n`, in `K⟦t⟧`,

`Hilb(Sym(M)^G, t) = #G⁻¹ ∑_{g ∈ G} ∑ₙ tr(g | Symⁿ M) tⁿ`.

These identities hold for the dimensions cast into `K`. In characteristic zero they determine the
dimensions, and hence the Hilbert series; in characteristic `p` they determine the dimensions only
modulo `p`, and the left-hand side is the image of the Hilbert series in `K⟦t⟧`.

This is Molien's formula in trace form. Each inner series is the graded trace of `g` on the
symmetric algebra. Since `g ^ #G = 1` and `#G` is invertible in `K`, the graded trace formula for
endomorphisms of finite order
(`Module.End.mk_trace_homogeneousSubmoduleMapₛₗ_mul_reverse_charpoly_of_pow_eq_one`) identifies it
with `det(1 - t g | M)⁻¹`, the inverse of the reverse of the characteristic polynomial of `g`.
Substituting gives **Molien's formula**

`Hilb(Sym(M)^G, t) = #G⁻¹ ∑_{g ∈ G} det(1 - t g | M)⁻¹`

in `K⟦t⟧`, over any field in which `#G` is invertible: the eigenvalues of the elements of `G` need
not lie in `K`. Applied to the contragredient representation `ρ.dual` on `M = V*`, it computes the
Hilbert series of the ring of polynomial invariants on `V`.

The action of `g` on `Symⁿ M` is written `homogeneousSubmoduleMapₛₗ (ρ g) n`, the map induced by
`ρ g` on degree `n` (`Representation.symmetricAlgebraHomogeneous_apply`).

## Main results

* `Representation.trace_averageMap_symmetricAlgebraHomogeneous`: the trace of the Reynolds
  operator on `Symⁿ M` is equal in `K` to the dimension of the degree-`n` invariants.
* `Representation.finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule`: the dimension of
  the degree-`n` invariants, cast into `K`, is the average over `G` of the traces on `Symⁿ M`.
* `Representation.mk_finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule`: Molien's
  formula in trace form, as an identity of formal power series over `K`.
* `mk_finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule_eq_sum_inv_reverse_charpoly`:
  (in the namespace `Representation`) Molien's formula, with the graded traces replaced by
  `det(1 - t g | M)⁻¹`.

## References

* T. Molien, *Über die Invarianten der linearen Substitutionsgruppen*, Sitzungsber. König.
  Preuss. Akad. Wiss. (1897), 1152–1156.
* R. P. Stanley, *Invariants of finite groups and their applications to combinatorics*,
  Bull. Amer. Math. Soc. (N.S.) **1** (1979), 475–511, Theorem 2.1.
* L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995), Section 4.3.
-/

public section

open TauCeti.SymmetricAlgebra

namespace Representation

variable {K G M : Type*} [Field K] [Group G] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
variable (ρ : Representation K G M) [Fintype G] [Invertible (Fintype.card G : K)]

/-- **The trace of the Reynolds operator.** On the degree-`n` component `Symⁿ M`, the Reynolds
operator (the averaging projection of the degree-`n` representation) has trace equal in `K` to
the dimension (cast into `K`) of the degree-`n` part of the invariant subalgebra. -/
theorem trace_averageMap_symmetricAlgebraHomogeneous (n : ℕ) :
    LinearMap.trace K _ (ρ.symmetricAlgebraHomogeneous n).averageMap =
      Module.finrank K
        ↥(Subalgebra.toSubmodule ρ.symmetricAlgebraInvariants ⊓ homogeneousSubmodule K M n) := by
  -- Instance search cannot apply `Submodule.addCommGroup` to `Symⁿ M`, whose module structure
  -- comes from the semiring `Sym M`, so it does not reach `Module.Free.of_divisionRing` for the
  -- subspaces of `Symⁿ M` that `LinearMap.IsProj.trace` needs to be free.
  have := Module.Free.of_divisionRing K (ρ.symmetricAlgebraHomogeneous n).invariants
  have := Module.Free.of_divisionRing K (LinearMap.ker (ρ.symmetricAlgebraHomogeneous n).averageMap)
  rw [(isProj_averageMap _).trace, finrank_invariants_symmetricAlgebraHomogeneous]

/-- **Molien's formula, degreewise.** The dimension of the degree-`n` part of the invariant
subalgebra, cast into `K`, is equal in `K` to the average over the group of the traces
`tr(g | Symⁿ M)`. In characteristic zero this determines the dimension; in characteristic `p` it
determines it only modulo `p`.

This is the instance on `Symⁿ M` of the character formula
`Representation.card_inv_mul_sum_char_eq_finrank` for the dimension of the invariants, stated
with the normalisation `⅟#G` of the Reynolds operator and the degree-`n` maps
`homogeneousSubmoduleMapₛₗ (ρ g) n`. -/
theorem finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule (n : ℕ) :
    (Module.finrank K
        ↥(Subalgebra.toSubmodule ρ.symmetricAlgebraInvariants ⊓ homogeneousSubmodule K M n) : K) =
      ⅟(Fintype.card G : K) *
        ∑ g : G, LinearMap.trace K _ (homogeneousSubmoduleMapₛₗ (ρ g) n) := by
  rw [← trace_averageMap_symmetricAlgebraHomogeneous, averageMap_eq_invOf_card_smul_norm,
    map_smul, norm, map_sum, smul_eq_mul]
  simp only [symmetricAlgebraHomogeneous_apply]

/-- **Molien's formula**, trace form: the image in `K⟦X⟧` of the Hilbert series of the invariant
subalgebra (its coefficients are the dimensions of the homogeneous components, cast into `K`) is
the average over the group of the graded traces `∑ₙ tr(g | Symⁿ M) tⁿ`. In characteristic zero
this determines the Hilbert series. -/
theorem mk_finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule :
    PowerSeries.mk (fun n ↦ (Module.finrank K
        ↥(Subalgebra.toSubmodule ρ.symmetricAlgebraInvariants ⊓ homogeneousSubmodule K M n) : K)) =
      ⅟(Fintype.card G : K) •
        ∑ g : G,
          PowerSeries.mk fun n ↦ LinearMap.trace K _ (homogeneousSubmoduleMapₛₗ (ρ g) n) := by
  ext n
  rw [PowerSeries.coeff_mk, finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule,
    PowerSeries.coeff_smul, map_sum, smul_eq_mul]
  simp only [PowerSeries.coeff_mk]

/-- **Molien's formula**: the image in `K⟦X⟧` of the Hilbert series of the invariant subalgebra
is the average over the group of the inverses of `det(1 - t g | M)`, the reverse of the
characteristic polynomial of `ρ g`:
`Hilb(Sym(M)^G, t) = #G⁻¹ ∑_{g ∈ G} det(1 - t g | M)⁻¹`.

The field `K` is arbitrary, subject only to `#G` being invertible in it; in characteristic zero
this determines the Hilbert series. -/
theorem mk_finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule_eq_sum_inv_reverse_charpoly :
    PowerSeries.mk (fun n ↦ (Module.finrank K
        ↥(Subalgebra.toSubmodule ρ.symmetricAlgebraInvariants ⊓ homogeneousSubmodule K M n) : K)) =
      ⅟(Fintype.card G : K) • ∑ g : G, ((ρ g).charpoly.reverse : PowerSeries K)⁻¹ := by
  rw [mk_finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule]
  refine congrArg _ (Finset.sum_congr rfl fun g _ ↦ ?_)
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · refine Module.End.mk_trace_homogeneousSubmoduleMapₛₗ_mul_reverse_charpoly_of_pow_eq_one
      (Invertible.ne_zero (Fintype.card G : K)) ?_
    rw [← map_pow, pow_card_eq_one, map_one]
  · simp [Polynomial.coeff_zero_reverse, (LinearMap.charpoly_monic (ρ g)).leadingCoeff]

end Representation
