/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import TauCeti.LinearAlgebra.Matrix.RowLattice
public import TauCeti.RingTheory.DiscreteValuationRing.Length
public import TauCeti.RingTheory.MatlisDuality.PrincipalIdealRing

/-!
# Matlis duality over a discrete valuation ring and lengths of orthogonals in `(K/O)ⁿ`

Let `O` be a discrete valuation ring with fraction field `K`. Matlis duality over a principal
ideal domain (`TauCeti.length_linearMap_fractionRing_quotient`) shows that `Hom_O(-, K/O)`
preserves lengths; over `O`, `Hom_O(O/a, K/O)` has length `v(a)`. Applied to quotients of `Oⁿ`,
this computes the length of the orthogonal in `(K/O)ⁿ` of a submodule `R ⊆ Oⁿ` under the pairing
`⟨v, u⟩ = ∑ i, v i • u i` (Mathlib's `Submodule.orthogonalBilin` for
`(Fintype.bilinearCombination O O).flip`): it is the colength of `R`. For the span of
the rows of a square matrix `M` the orthogonal is the kernel of `M` acting on `(K/O)ⁿ`, and its
length is the valuation of `det M`, both infinite when `det M = 0`.

## Main results

* `IsDiscreteValuationRing.length_linearMap_quotient_span_singleton`: for `a ≠ 0`,
  `Hom_O(O/a, K/O)` has length `v(a)`.
* `IsDiscreteValuationRing.length_torsionBy_quotient_span_singleton_le`: the elements of `O/a`
  killed by `c` form a module of length at most `v(c)`.
* `IsDiscreteValuationRing.length_orthogonalBilin`: the orthogonal of `R ⊆ Oⁿ` in `(K/O)ⁿ` has
  length `length_O (Oⁿ/R)`.
* `Matrix.length_ker_eq_addVal_det`: the kernel of a square matrix `M` acting on `(K/O)ⁿ` has
  length `v(det M)`.

## Provenance

The kernel bound `length ker ≤ v(det M)` on `(O/p)ⁿ` is `New.length_ker_le_addVal_det` in
grh-lean (https://github.com/lsernau/grh-lean, file
`src/Lib/General/Algebra/FittingIdealsAndLengths.lean`, Apache 2.0, Copyright 2026 Anthropic,
PBC), proved there by Smith normal form. The equality `length ker = v(det M)` on `(K/O)ⁿ`, with
`K = FractionRing O`, is `Formalism.NG.lenKer` in L. Alpöge's Lean formalization of the
Riemann hypothesis project (https://github.com/leanprover-community/riemann-hypothesis, file
`src/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean`); the
statement `Matrix.length_ker_eq_addVal_det` follows it, for any fraction field `K`. The proof here
goes through Matlis duality and the cokernel length formula
`Matrix.length_quotient_range_mulVecLin_eq_ord_det`.

## References

* E. Matlis, *Injective modules over Noetherian rings*, Pacific J. Math. 8 (1958).
* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1.
-/

public section

open IsLocalRing LinearMap

namespace IsDiscreteValuationRing

universe u v

variable {O : Type u} {K : Type v} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]

/-- For `a ≠ 0`, `Hom_O(O/a, K/O)` has length `v(a)`. -/
theorem length_linearMap_quotient_span_singleton {a : O} (ha : a ≠ 0) :
    Module.length O (O ⧸ Ideal.span {a} →ₗ[O] K ⧸ range (Algebra.linearMap O K)) =
      addVal O a := by
  rw [((Ideal.span {a}).quotientLinearMapEquivTorsionBySet _).length_eq,
    ← (TauCeti.quotientEquivTorsionBySet ha).length_eq, ← Ring.ord, Ring.ord_eq_addVal]

omit [Field K] [Algebra O K] [IsFractionRing O K] in
/-- The elements of `O ⧸ (a)` killed by `c` form a module of length at most `v(c)`. -/
theorem length_torsionBy_quotient_span_singleton_le (a c : O) :
    Module.length O (Submodule.torsionBy O (O ⧸ Ideal.span {a}) c) ≤ addVal O c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne a 0 with rfl | ha
  · -- `O ⧸ (0)` has no nonzero element killed by `c ≠ 0`.
    refine (Module.length_eq_zero_iff.2 ⟨fun x y ↦ ?_⟩).trans_le zero_le
    have h (w : Submodule.torsionBy O (O ⧸ Ideal.span {(0 : O)}) c) : w = 0 := by
      obtain ⟨w, hw⟩ := w
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective w
      simp [Algebra.smul_def, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hc] at hw
      ext
      simp [hw]
    rw [h x, h y]
  -- `O ⧸ (a)` embeds in `K/O`, whose elements killed by `c` form a copy of `O ⧸ (c)`.
  let K := FractionRing O
  let ι : O ⧸ Ideal.span {a} →ₗ[O] K ⧸ range (Algebra.linearMap O K) :=
    Submodule.subtype _ ∘ₗ (TauCeti.quotientEquivTorsionBySet (K := K) ha).toLinearMap
  have hι : Function.Injective ι := Subtype.val_injective.comp (LinearEquiv.injective _)
  have hmaps : ∀ x ∈ Submodule.torsionBy O _ c, ι x ∈ Submodule.torsionBy O _ c := fun x hx ↦ by
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    rw [← map_smul, hx, map_zero]
  calc Module.length O (Submodule.torsionBy O (O ⧸ Ideal.span {a}) c)
      ≤ Module.length O (Submodule.torsionBy O (K ⧸ range (Algebra.linearMap O K)) c) :=
        Module.length_le_of_injective (ι.restrict hmaps) fun x y hxy ↦
          Subtype.ext (hι congr(Subtype.val $hxy))
    _ = addVal O c := by
        rw [← Submodule.torsionBySet_span_singleton_eq,
          ← (TauCeti.quotientEquivTorsionBySet hc).length_eq, ← Ring.ord, Ring.ord_eq_addVal]

variable {ι : Type*} [Fintype ι]

/-- **The orthogonal in `(K/O)^ι` of a submodule `R ⊆ O^ι` has the colength of `R`.** The
orthogonal is `Hom_O(O^ι / R, K/O)`, and Matlis duality preserves lengths. -/
theorem length_orthogonalBilin (R : Submodule O (ι → O)) :
    Module.length O (R.orthogonalBilin
        (Fintype.bilinearCombination O O (M := K ⧸ range (Algebra.linearMap O K))).flip) =
      Module.length O ((ι → O) ⧸ R) := by
  classical
  rw [(R.orthogonalPiEquiv _).length_eq,
    TauCeti.length_linearMap_fractionRing_quotient (not_isField O)]

end IsDiscreteValuationRing

namespace Matrix

open IsDiscreteValuationRing

variable {ι : Type*} {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] [Fintype ι] [DecidableEq ι]

/-- **The kernel of a square matrix on `(K/O)^ι` has length `v(det M)`.** The kernel of `M`
acting on `(K/O)^ι`, the orthogonal of the rows of `M`, has length the valuation of `det M`, both
sides infinite when `det M = 0`. -/
theorem length_ker_eq_addVal_det (M : Matrix ι ι O) :
    Module.length O (M.ker (K ⧸ range (Algebra.linearMap O K))) =
      addVal O M.det := by
  rw [ker_eq_orthogonalBilin, length_orthogonalBilin,
    length_quotient_span_range_eq_addVal_det]

end Matrix
