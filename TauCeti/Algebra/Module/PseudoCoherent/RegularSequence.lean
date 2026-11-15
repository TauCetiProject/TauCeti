/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import TauCeti.Algebra.Module.PseudoCoherent.FiniteProjectiveDimension
import Mathlib.RingTheory.Regular.Category

/-!
# Quotients by weakly regular sequences have finite projective dimension

If `x` is a nonzerodivisor on `M`, the exact sequence `0 → M → M → M ⧸ x M → 0`, the first map
being multiplication by `x`, shows that `M ⧸ x M` is `(m + 1)`-fpd whenever `M` is `m`-fpd.
Iterating along a weakly `M`-regular sequence `f₁, …, f_r`, the quotient `M ⧸ (f₁, …, f_r) M` is
`(m + r)`-fpd. For `M = R` this says that `R ⧸ (f₁, …, f_r)` is `r`-fpd, hence pseudocoherent, and
the ideal `(f₁, …, f_r)` is `(r - 1)`-fpd. These are the finite projective resolutions that a
Koszul complex of a weakly regular sequence provides, in the form used by Kedlaya–Liu.

## Main results

* `TauCeti.Module.IsFPD.quotSMulTop`: if `M` is `m`-fpd and `x` is `M`-regular, then `M ⧸ x M` is
  `(m + 1)`-fpd.
* `TauCeti.Module.IsFPD.quotient_ofList_smul_top`: if `M` is `m`-fpd and `rs` is weakly
  `M`-regular, then `M ⧸ (rs) M` is `(m + rs.length)`-fpd.
* `TauCeti.Module.isFPD_quotient_ofList`: for a weakly regular sequence `rs` on `R`, the quotient
  `R ⧸ (rs)` is `rs.length`-fpd.
* `TauCeti.Module.isFPD_ofList`: for a weakly regular sequence `rs` on `R`, the ideal `(rs)` is
  `(rs.length - 1)`-fpd.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §1.1,
  Remark 1.1.6.
* [The Stacks Project, Tag 062F](https://stacks.math.columbia.edu/tag/062F)
-/

public section

namespace TauCeti.Module

open LinearMap RingTheory.Sequence Pointwise

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {m : ℕ}

/-- **Dividing by a regular element raises the fpd degree by one.** If `M` is `m`-fpd and `x` is a
nonzerodivisor on `M`, then `M ⧸ x M` is `(m + 1)`-fpd (Kedlaya–Liu II, Remark 1.1.6). -/
theorem IsFPD.quotSMulTop (h : IsFPD R M m) {x : R} (hx : IsSMulRegular M x) :
    IsFPD R (QuotSMulTop x M) (m + 1) :=
  IsFPD.cokernel (f := lsmul R M x) hx (exact_lsmul_mkQ_smul_top M x) (Submodule.mkQ_surjective _)
    h (h.mono m.le_succ)

/-- **Quotients by weakly regular sequences.** If `M` is `m`-fpd and `rs` is a weakly `M`-regular
sequence, then `M ⧸ (rs) M` is `(m + rs.length)`-fpd. -/
theorem IsFPD.quotient_ofList_smul_top (h : IsFPD R M m) {rs : List R}
    (hrs : IsWeaklyRegular M rs) :
    IsFPD R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) (m + rs.length) := by
  induction rs generalizing M m with
  | nil =>
    exact h.of_equiv (Submodule.quotEquivOfEqBot _ (by simp)).symm
  | cons r rs ih =>
    obtain ⟨hr, hrs⟩ := (isWeaklyRegular_cons_iff M r rs).mp hrs
    rw [List.length_cons, ← add_assoc, add_right_comm]
    exact (ih (h.quotSMulTop hr) hrs).of_equiv
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs).symm

/-- **The quotient by a weakly regular sequence is fpd.** If `rs` is a weakly regular sequence on
`R`, then `R ⧸ (rs)` has a resolution of length `rs.length` by finitely generated projective
modules; in particular it is pseudocoherent. -/
theorem isFPD_quotient_ofList {rs : List R} (hrs : IsWeaklyRegular R rs) :
    IsFPD R (R ⧸ Ideal.ofList rs) rs.length := by
  simpa using ((IsFPD.of_projective (R := R) (M := R)).quotient_ofList_smul_top hrs).of_equiv
    (Submodule.quotEquivOfEq _ _ (by simp))

/-- **The ideal of a weakly regular sequence is fpd.** If `rs` is a weakly regular sequence on `R`,
then the ideal `(rs)` is `(rs.length - 1)`-fpd. For the empty sequence the ideal is zero. -/
theorem isFPD_ofList {rs : List R} (hrs : IsWeaklyRegular R rs) :
    IsFPD R (Ideal.ofList rs) (rs.length - 1) := by
  cases rs with
  | nil => exact IsFPD.of_projective.of_equiv (.ofEq ⊥ _ Ideal.ofList_nil.symm)
  | cons r rs =>
    rw [List.length_cons, Nat.add_sub_cancel]
    exact ((IsFPD.succ_iff_ker (Submodule.mkQ_surjective _)).mp
      (isFPD_quotient_ofList hrs)).of_equiv (.ofEq _ _ (Submodule.ker_mkQ _))

end TauCeti.Module
