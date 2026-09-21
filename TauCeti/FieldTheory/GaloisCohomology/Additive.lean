/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.FieldTheory.Galois.NormalBasis
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced

/-!
# The additive group of a finite Galois extension is cohomologically trivial

Let `L/K` be a finite Galois extension with Galois group `Γ = Gal(L/K)`. A normal basis
identifies the additive representation on `L` with the representation induced from the trivial
subgroup. Consequently every Tate cohomology group of `Γ`, and of every subgroup of `Γ`, with
coefficients in `L` vanishes. This is the additive counterpart of Hilbert's theorem 90 and the
input that makes the units of an unramified extension of local fields cohomologically trivial,
through the filtration of the units by the additive graded pieces of the maximal ideal.

The coefficient ring is an arbitrary commutative ring `R` acting on `L` through `K`. The two cases
in use are `R = K`, where the statement is the classical one about `K`-vector spaces, and `R = ℤ`,
where the representation is Mathlib's `Rep.ofAlgebraAut K L` and the Tate groups are the abelian
groups that a class formation is built from.

## Main results

* `TauCeti.isZero_tateCohomology_galoisAddRep` and
  `TauCeti.isZero_tateCohomology_res_galoisAddRep`: every Tate cohomology group of `Gal(L/K)`,
  and of any subgroup of it, with coefficients in `L` vanishes.
* `TauCeti.isZero_groupCohomology_galoisAddRep`: the additive form of Hilbert's theorem 90 and
  its higher analogues, `Hⁿ(Gal(L/K), L) = 0` for `n ≥ 1`.
* `TauCeti.mem_coinvariantsKer_of_trace_eq_zero`: the degree `-1` reading, that an element of
  trace zero is a sum of differences `σ y - y`.

## References

* J-P. Serre, *Local Fields*, Chapter X, §1, Proposition 1.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, §1 and Chapter III, §1.
-/

public noncomputable section

open CategoryTheory Limits Rep

namespace TauCeti

universe u

variable (R K L : Type u) [CommRing R] [Field K] [Field L] [Algebra K L]
  [Algebra R K] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]

/-- **The additive group of a finite Galois extension is cohomologically trivial**: every Tate
cohomology group of `Gal(L/K)` with coefficients in `L` vanishes. -/
theorem isZero_tateCohomology_galoisAddRep (r : ℤ) :
    IsZero (tateCohomology (galoisAddRep R K L) r) :=
  (TateCohomology.isZero_indBot K r).of_iso
    ((tateCohomologyFunctor r).mapIso (galoisAddRepIsoIndBot R K L))

/-- Every Tate cohomology group of a subgroup of `Gal(L/K)` with coefficients in `L` vanishes:
cohomological triviality is inherited by subgroups. -/
theorem isZero_tateCohomology_res_galoisAddRep (H : Subgroup Gal(L/K)) [Fintype H] (r : ℤ) :
    IsZero (tateCohomology (Rep.res H.subtype (galoisAddRep R K L)) r) :=
  (TateCohomology.isZero_res_indBot H K r).of_iso
    ((tateCohomologyFunctor r).mapIso ((Rep.resFunctor H.subtype).mapIso
      (galoisAddRepIsoIndBot R K L)))

/-- **Additive Hilbert 90 and its higher analogues**: the group cohomology of `Gal(L/K)` with
coefficients in `L` vanishes in every positive degree. -/
theorem isZero_groupCohomology_galoisAddRep (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (galoisAddRep R K L) n) :=
  (isZero_tateCohomology_galoisAddRep R K L n).of_iso
    ((_root_.TateCohomology.isoGroupCohomology n).app (galoisAddRep R K L)).symm

/-- The norm of the Galois representation on the additive group of `L` is the field trace. -/
theorem norm_ofDistribMulAction_eq_algebraMap_trace (x : L) :
    (Representation.ofDistribMulAction R Gal(L/K) L).norm x =
      algebraMap K L (Algebra.trace K L x) := by
  rw [Representation.norm_ofDistribMulAction_eq, _root_.trace_eq_sum_automorphisms]
  exact Finset.sum_congr rfl fun σ _ ↦ σ.smul_def x

/-- **Additive Hilbert 90 in degree `-1`**: an element of trace zero lies in the augmentation
submodule, that is, it is a sum of differences `σ y - y` with `σ` in the Galois group. -/
theorem mem_coinvariantsKer_of_trace_eq_zero {x : L} (hx : Algebra.trace K L x = 0) :
    x ∈ Representation.Coinvariants.ker (Representation.ofDistribMulAction R Gal(L/K) L) := by
  have hker : x ∈ LinearMap.ker (Representation.ofDistribMulAction R Gal(L/K) L).norm := by
    rw [LinearMap.mem_ker, norm_ofDistribMulAction_eq_algebraMap_trace, hx, map_zero]
  -- Degree `-1` Tate cohomology is the quotient of the norm kernel by the augmentation
  -- submodule, and it vanishes, so the two submodules agree.
  have : Subsingleton (tateCohomology (galoisAddRep R K L) (-1)) :=
    ModuleCat.subsingleton_of_isZero (isZero_tateCohomology_galoisAddRep R K L (-1))
  exact Submodule.mem_comap.1
    ((TateCohomology.HNegOneπ_eq_zero_iff (M := galoisAddRep R K L) ⟨x, hker⟩).1
      (Subsingleton.elim _ _))

end TauCeti
