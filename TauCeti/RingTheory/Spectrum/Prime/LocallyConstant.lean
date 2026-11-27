/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.RingTheory.Idempotents.Module
import TauCeti.RingTheory.Idempotents.Prime
import TauCeti.RingTheory.Spectrum.Prime.Topology

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
`TauCeti.RingTheory.Spectrum.Prime.Rank.Decomposition`.

## Main declarations

* `PrimeSpectrum.fiberIdempotent hf a`: the idempotent whose basic open set is `f ⁻¹' {a}`.
* `PrimeSpectrum.eq_fiberIdempotent_iff`: it is the only idempotent with this basic open set.
* `PrimeSpectrum.mem_basicOpen_fiberIdempotent`, `PrimeSpectrum.fiberIdempotent_mem_iff`: a prime
  `p` lies in its basic open set exactly when `f p = a`, and contains it exactly when `f p ≠ a`.
* `PrimeSpectrum.fiberIdempotent_eq_zero_iff`, `PrimeSpectrum.fiberIdempotent_eq_one_iff`: it
  vanishes exactly off the range of `f`, and is `1` exactly when `f` is constantly `a`.
* `PrimeSpectrum.completeOrthogonalIdempotents_fiberIdempotent`: the fibre idempotents of a finite
  set of values containing the range of `f` form a complete orthogonal family.
* `PrimeSpectrum.isInternal_smul_top_fiberIdempotent`: the resulting decomposition
  `M = ⨁ₐ eₐ • M` of an arbitrary `R`-module.
* `PrimeSpectrum.projective_smul_top_fiberIdempotent`: each piece `eₐ • M` of a projective module
  is projective.

## References

* The Stacks Project, Tag 00EE, *Idempotents and clopen subsets of the spectrum*.
-/

public section

open scoped Pointwise

open TopologicalSpace

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

/-- A prime lies in the basic open set of the fibre idempotent at `a` exactly when `f` takes the
value `a` there. -/
theorem mem_basicOpen_fiberIdempotent {a : α} {p : PrimeSpectrum R} :
    p ∈ basicOpen (fiberIdempotent hf a) ↔ f p = a :=
  Set.ext_iff.1 (coe_basicOpen_fiberIdempotent hf a) p

/-- A prime contains the fibre idempotent at `a` exactly when `f` does not take the value `a`
there. -/
@[simp]
theorem fiberIdempotent_mem_iff {a : α} {p : PrimeSpectrum R} :
    fiberIdempotent hf a ∈ p.asIdeal ↔ f p ≠ a := by
  simpa using (mem_basicOpen_fiberIdempotent hf (a := a) (p := p)).not

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

/-- The fibre idempotent at `a` vanishes exactly when `a` is not a value of `f`. -/
@[simp]
theorem fiberIdempotent_eq_zero_iff {a : α} : fiberIdempotent hf a = 0 ↔ a ∉ Set.range f := by
  simp [← basicOpen_eq_bot_iff_of_isIdempotentElem (isIdempotentElem_fiberIdempotent hf a),
    SetLike.ext_iff]

/-- The fibre idempotent at `a` is `1` exactly when `f` is constantly `a`. -/
@[simp]
theorem fiberIdempotent_eq_one_iff {a : α} : fiberIdempotent hf a = 1 ↔ ∀ p, f p = a := by
  rw [eq_comm, eq_fiberIdempotent_iff hf .one]
  simp [Set.ext_iff]

/-- Fibre idempotents at distinct values are orthogonal. -/
theorem fiberIdempotent_mul_fiberIdempotent_of_ne {a b : α} (hab : a ≠ b) :
    fiberIdempotent hf a * fiberIdempotent hf b = 0 := by
  refine (basicOpen_eq_bot_iff_of_isIdempotentElem
    ((isIdempotentElem_fiberIdempotent hf a).mul (isIdempotentElem_fiberIdempotent hf b))).1
    (eq_bot_iff.2 fun p hp ↦ hab ?_)
  simp only [basicOpen_mul, Opens.mem_inf, mem_basicOpen_fiberIdempotent] at hp
  exact hp.1.symm.trans hp.2

/-- **The fibre idempotents form a complete orthogonal family**: over a finite set `s` of values
containing the range of `f`, the fibre idempotents are orthogonal and add up to `1`. -/
theorem completeOrthogonalIdempotents_fiberIdempotent {s : Finset α}
    (hs : Set.range f ⊆ s) :
    CompleteOrthogonalIdempotents fun a : s ↦ fiberIdempotent hf a := by
  classical
  have ho : OrthogonalIdempotents fun a : s ↦ fiberIdempotent hf a :=
    ⟨fun a ↦ isIdempotentElem_fiberIdempotent hf a,
      fun a b hab ↦ fiberIdempotent_mul_fiberIdempotent_of_ne hf (Subtype.coe_injective.ne hab)⟩
  refine ⟨ho, (sub_eq_zero.1 ((basicOpen_eq_bot_iff_of_isIdempotentElem
    ho.isIdempotentElem_sum.one_sub).1 (eq_bot_iff.2 fun p hp ↦ (hp ?_).elim))).symm⟩
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
theorem isInternal_smul_top_fiberIdempotent [DecidableEq α] (M : Type*) [AddCommMonoid M]
    [Module R M] {s : Finset α} (hs : Set.range f ⊆ s) :
    DirectSum.IsInternal fun a : s ↦ fiberIdempotent hf a • (⊤ : Submodule R M) :=
  TauCeti.isInternal_smul_top (completeOrthogonalIdempotents_fiberIdempotent hf hs)

variable {hf} in
/-- Each piece `eₐ • M` cut out by a fibre idempotent of a projective module is projective: it is
a direct summand of `M`. -/
instance projective_smul_top_fiberIdempotent {M : Type*} [AddCommMonoid M] [Module R M]
    [Module.Projective R M] {a : α} :
    Module.Projective R ↥(fiberIdempotent hf a • (⊤ : Submodule R M)) :=
  (isIdempotentElem_fiberIdempotent hf a).projective_smul_top

end PrimeSpectrum
