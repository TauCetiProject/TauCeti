/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.RingTheory.Idempotents.Module

/-!
# Fibre idempotents of locally constant functions on a prime spectrum

Let `R` be a commutative ring and `f` a locally constant function on `Spec R`. Each fibre
`f ⁻¹' {a}` is clopen, so by Mathlib's correspondence between clopen subsets of `Spec R` and
idempotents of `R` (`PrimeSpectrum.isIdempotentElemEquivClopens`) it is the basic open set of a
unique idempotent `PrimeSpectrum.fiberIdempotent hf a`. Distinct fibres are disjoint, so these
idempotents are orthogonal, and the fibres cover `Spec R`, so the idempotents of any finite set of
values containing the range of `f` add up to `1`. Such a complete orthogonal family splits every
`R`-module `M` into the pieces `eₐ • M`, one for each value `a`.

The range of a locally constant function on the quasi-compact space `Spec R` is finite
(`IsLocallyConstant.range_finite`), so a finite set of values containing it always exists. The main
example is the rank `Module.rankAtStalk M` of a finite projective module, whose fibre idempotents
split `M` into pieces of constant rank; see
`TauCeti.RingTheory.Spectrum.Prime.RankDecomposition`.

## Main declarations

* `IsIdempotentElem.one_sub_mem_iff_notMem`: a prime ideal contains exactly one of `e` and
  `1 - e`.
* `PrimeSpectrum.fiberIdempotent hf a`: the idempotent whose basic open set is `f ⁻¹' {a}`.
* `PrimeSpectrum.eq_fiberIdempotent_iff`: it is the only idempotent with this basic open set.
* `PrimeSpectrum.fiberIdempotent_mem_iff`: a prime `p` contains it exactly when `f p ≠ a`.
* `PrimeSpectrum.fiberIdempotent_eq_zero_iff`, `PrimeSpectrum.fiberIdempotent_eq_one_iff`: it
  vanishes exactly off the range of `f`, and is `1` exactly when `f` is constantly `a`.
* `PrimeSpectrum.completeOrthogonalIdempotents_fiberIdempotent`: the fibre idempotents of a finite
  set of values containing the range of `f` form a complete orthogonal family.
* `PrimeSpectrum.isInternal_smul_top_fiberIdempotent`: the resulting decomposition
  `M = ⨁ₐ eₐ • M` of an arbitrary `R`-module.

## References

* The Stacks Project, Tag 00EE, *Idempotents and clopen subsets of the spectrum*.
-/

public section

open scoped Pointwise

open TopologicalSpace

/-- A prime ideal contains exactly one of an idempotent `e` and its complement `1 - e`. -/
theorem IsIdempotentElem.one_sub_mem_iff_notMem {R : Type*} [Ring R] {e : R}
    (he : IsIdempotentElem e) {P : Ideal R} [hP : P.IsPrime] : 1 - e ∈ P ↔ e ∉ P := by
  refine ⟨fun h he' ↦ hP.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.add_mem he' h)),
    fun h ↦ (hP.mem_or_mem ?_).resolve_left h⟩
  rw [he.mul_one_sub_self]
  exact P.zero_mem

namespace PrimeSpectrum

variable {R : Type*} [CommRing R] {α : Type*} {f : PrimeSpectrum R → α}

/-- The **fibre idempotent** of a locally constant function `f` on `Spec R` at a value `a`: the
idempotent of `R` whose basic open set is the clopen fibre `f ⁻¹' {a}`. -/
noncomputable def fiberIdempotent (hf : IsLocallyConstant f) (a : α) : R :=
  (isIdempotentElemEquivClopens.symm ⟨f ⁻¹' {a}, hf.isClopen_fiber a⟩ :
    {e : R // IsIdempotentElem e}).val

variable (hf : IsLocallyConstant f)

/-- The fibre idempotent is idempotent. -/
theorem isIdempotentElem_fiberIdempotent (a : α) : IsIdempotentElem (fiberIdempotent hf a) :=
  (isIdempotentElemEquivClopens.symm ⟨f ⁻¹' {a}, hf.isClopen_fiber a⟩).property

/-- The basic open set of the fibre idempotent at `a` is the fibre of `f` over `a`. -/
theorem coe_basicOpen_fiberIdempotent (a : α) :
    (basicOpen (fiberIdempotent hf a) : Set (PrimeSpectrum R)) = f ⁻¹' {a} :=
  congrArg SetLike.coe (basicOpen_isIdempotentElemEquivClopens_symm _)

/-- A prime contains the fibre idempotent at `a` exactly when `f` does not take the value `a`
there. -/
@[simp]
theorem fiberIdempotent_mem_iff {a : α} {p : PrimeSpectrum R} :
    fiberIdempotent hf a ∈ p.asIdeal ↔ f p ≠ a := by
  rw [← not_iff_not, not_not, ← mem_basicOpen, ← SetLike.mem_coe,
    coe_basicOpen_fiberIdempotent, Set.mem_preimage, Set.mem_singleton_iff]

/-- **Characterization of the fibre idempotent**: an idempotent equals the fibre idempotent at `a`
exactly when its basic open set is the fibre of `f` over `a`. -/
theorem eq_fiberIdempotent_iff {e : R} (he : IsIdempotentElem e) {a : α} :
    e = fiberIdempotent hf a ↔ (basicOpen e : Set (PrimeSpectrum R)) = f ⁻¹' {a} := by
  refine ⟨fun h ↦ h ▸ coe_basicOpen_fiberIdempotent hf a, fun h ↦ ?_⟩
  have := isIdempotentElemEquivClopens.injective (a₁ := ⟨e, he⟩)
    (a₂ := ⟨_, isIdempotentElem_fiberIdempotent hf a⟩)
    (Clopens.ext (by
      rw [coe_isIdempotentElemEquivClopens_apply, coe_isIdempotentElemEquivClopens_apply,
        coe_basicOpen_fiberIdempotent, h]))
  exact congrArg Subtype.val this

/-- An idempotent lies in every prime ideal only if it is zero. -/
private theorem eq_zero_of_basicOpen_eq_empty {e : R} (he : IsIdempotentElem e)
    (h : (basicOpen e : Set (PrimeSpectrum R)) = ∅) : e = 0 :=
  he.eq_zero_of_isNilpotent <| (basicOpen_eq_bot_iff e).1 <| SetLike.coe_injective h

/-- The fibre idempotent at `a` vanishes exactly when `a` is not a value of `f`. -/
@[simp]
theorem fiberIdempotent_eq_zero_iff {a : α} : fiberIdempotent hf a = 0 ↔ a ∉ Set.range f := by
  rw [eq_comm, eq_fiberIdempotent_iff hf .zero, basicOpen_zero, Opens.coe_bot, eq_comm,
    Set.preimage_singleton_eq_empty]

/-- The fibre idempotent at `a` is `1` exactly when `f` is constantly `a`. -/
@[simp]
theorem fiberIdempotent_eq_one_iff {a : α} : fiberIdempotent hf a = 1 ↔ ∀ p, f p = a := by
  rw [eq_comm, eq_fiberIdempotent_iff hf .one, basicOpen_one, Opens.coe_top, eq_comm,
    Set.eq_univ_iff_forall]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]

/-- Fibre idempotents at distinct values are orthogonal. -/
theorem fiberIdempotent_mul_fiberIdempotent_of_ne {a b : α} (hab : a ≠ b) :
    fiberIdempotent hf a * fiberIdempotent hf b = 0 := by
  refine eq_zero_of_basicOpen_eq_empty
    ((isIdempotentElem_fiberIdempotent hf a).mul (isIdempotentElem_fiberIdempotent hf b)) ?_
  rw [basicOpen_mul, Opens.coe_inf, coe_basicOpen_fiberIdempotent, coe_basicOpen_fiberIdempotent,
    ← Set.preimage_inter, Set.singleton_inter_eq_empty.2 hab, Set.preimage_empty]

/-- **The fibre idempotents form a complete orthogonal family**: over a finite set `s` of values
containing the range of `f`, the fibre idempotents are orthogonal and add up to `1`. -/
theorem completeOrthogonalIdempotents_fiberIdempotent {s : Finset α}
    (hs : Set.range f ⊆ s) :
    CompleteOrthogonalIdempotents fun a : s ↦ fiberIdempotent hf a := by
  classical
  have ho : OrthogonalIdempotents fun a : s ↦ fiberIdempotent hf a :=
    ⟨fun a ↦ isIdempotentElem_fiberIdempotent hf a,
      fun a b hab ↦ fiberIdempotent_mul_fiberIdempotent_of_ne hf (Subtype.coe_injective.ne hab)⟩
  refine ⟨ho, (sub_eq_zero.1 (eq_zero_of_basicOpen_eq_empty ho.isIdempotentElem_sum.one_sub
    (Set.eq_empty_of_forall_notMem fun p hp ↦ hp ?_))).symm⟩
  -- At a prime `p`, the term at the value `f p` is `1` modulo `p` and every other term lies in `p`.
  let b : s := ⟨f p, hs ⟨p, rfl⟩⟩
  have hb' : 1 - fiberIdempotent hf (f p) ∈ p.asIdeal :=
    (isIdempotentElem_fiberIdempotent hf (f p)).one_sub_mem_iff_notMem.2 (by simp)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), sub_add_eq_sub_sub]
  refine p.asIdeal.sub_mem hb' (p.asIdeal.sum_mem fun a ha ↦ ?_)
  rw [fiberIdempotent_mem_iff]
  exact fun h ↦ Finset.ne_of_mem_erase ha (Subtype.ext h.symm)

/-- **Decomposition of a module along the fibres of a locally constant function**: over a finite
set `s` of values containing the range of `f`, every `R`-module `M` is the internal direct sum of
the pieces `eₐ • M` cut out by the fibre idempotents. The component of `x` at `a` is `eₐ • x`
(`TauCeti.coe_ofBijective_coeLinearMap_symm_apply_smul_top`). -/
theorem isInternal_smul_top_fiberIdempotent [DecidableEq α] (M : Type*) [AddCommGroup M]
    [Module R M] {s : Finset α} (hs : Set.range f ⊆ s) :
    DirectSum.IsInternal fun a : s ↦ fiberIdempotent hf a • (⊤ : Submodule R M) :=
  TauCeti.isInternal_smul_top (completeOrthogonalIdempotents_fiberIdempotent hf hs)

end PrimeSpectrum
