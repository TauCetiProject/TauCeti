/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic

/-!
# Local Sobolev classes reaching the boundary

`TauCeti.MemWkpLocHalf p U k u` requires weak derivatives through order `k` on the
interior of `U`, with local `Lᵖ` bounds on compact subsets of `U` itself. In particular,
when `U` is a relatively open subset of the closed upper half-plane, the test functions
stay in the open upper half-plane, but the integrability bounds reach the real axis.
Testing only compact subsets of the interior would lose this boundary control.

The definition is meaningful for any set `U`. On open sets it agrees with `MemWkpLoc`.
This file supplies restriction, almost-everywhere invariance, linear operations, decreasing
order and exponent, and continuous-linear composition. Restriction from an ambient open
neighbourhood gives boundary-reaching membership; in particular, globally `Cᵏ` maps,
including the identity and polynomials, satisfy this class at every exponent.
No extension across the boundary is asserted here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces on domains with boundary).
-/

public noncomputable section

open MeasureTheory TopologicalSpace

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {p q : ENNReal} {U V : Set ℂ} {f g : ℂ → F} {k l : ℕ} {Ω : Opens ℂ}

/-- Local Sobolev membership up to the boundary of `U`: weak derivatives are tested on
`interior U`, while every derivative through order `k` is `Lᵖ` on every compact subset of `U`.
For half-discs the bounds therefore reach the real axis. No boundary trace is prescribed. -/
def MemWkpLocHalf (p : ENNReal) (U : Set ℂ) :
    (k : ℕ) → {F : Type*} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (ℂ → F) → Prop
  | 0, _, _, _, f => MemLpLoc p U f
  | k + 1, F, _, _, f => MemLpLoc p U f ∧
      ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
        MemWkpLocHalf p U k D

/-- Order zero requires local `Lᵖ` bounds on compact sets reaching the boundary. -/
@[simp]
theorem memWkpLocHalf_zero_iff : MemWkpLocHalf p U 0 f ↔ MemLpLoc p U f := Iff.rfl

/-- Successor membership consists of a locally `Lᵖ` function and a weak derivative with
one fewer derivative, retaining the boundary-reaching bounds. -/
theorem memWkpLocHalf_succ_iff : MemWkpLocHalf p U (k + 1) f ↔ MemLpLoc p U f ∧
    ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      MemWkpLocHalf p U k D := Iff.rfl

/-- Boundary-reaching Sobolev membership includes boundary-reaching local `Lᵖ` membership. -/
theorem MemWkpLocHalf.memLpLoc (hf : MemWkpLocHalf p U k f) : MemLpLoc p U f := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

/-- A positive-order member has an interior weak derivative with boundary-reaching bounds. -/
theorem MemWkpLocHalf.exists_weakFDeriv (hf : MemWkpLocHalf p U (k + 1) f) :
    ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      MemWkpLocHalf p U k D := hf.2

/-- Positive-order membership retains completeness from the native weak-derivative relation. -/
theorem MemWkpLocHalf.completeSpace (hf : MemWkpLocHalf p U (k + 1) f) : CompleteSpace F := by
  obtain ⟨D, hD, _⟩ := hf.exists_weakFDeriv
  exact hD.completeSpace

/-- Restriction preserves both the interior weak derivatives and the boundary-reaching bounds. -/
theorem MemWkpLocHalf.mono (hf : MemWkpLocHalf p U k f) (hVU : V ⊆ U) :
    MemWkpLocHalf p V k f := by
  induction k generalizing F with
  | zero => exact hf.mono_set hVU
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.mono_set hVU, D, hD.mono (interior_mono hVU), ih hk⟩

/-- Almost-everywhere changes on the full set preserve the class, including its boundary bounds. -/
theorem MemWkpLocHalf.congr_ae (hf : MemWkpLocHalf p U k f)
    (hfg : f =ᵐ[volume.restrict U] g) : MemWkpLocHalf p U k g := by
  cases k with
  | zero => exact hf.congr_ae hfg
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.congr_ae hfg, D,
      hD.congr_ae (ae_mono (Measure.restrict_mono_set volume interior_subset) hfg), hk⟩

/-- Decreasing the integrability exponent preserves every boundary-reaching derivative order. -/
theorem MemWkpLocHalf.mono_exponent (hf : MemWkpLocHalf p U k f) (hqp : q ≤ p) :
    MemWkpLocHalf q U k f := by
  induction k generalizing F with
  | zero => exact hf.mono_exponent hqp
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.mono_exponent hqp, D, hD, ih hk⟩

/-- Dropping the top derivative preserves boundary-reaching membership. -/
theorem MemWkpLocHalf.of_succ (hf : MemWkpLocHalf p U (k + 1) f) :
    MemWkpLocHalf p U k f := by
  induction k generalizing F with
  | zero => exact hf.1
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp, D, hD, ih hk⟩

/-- Every smaller derivative order inherits boundary-reaching membership. -/
theorem MemWkpLocHalf.of_le (hf : MemWkpLocHalf p U k f) (hlk : l ≤ k) :
    MemWkpLocHalf p U l f := by
  induction hlk with
  | refl => exact hf
  | step h ih => exact ih hf.of_succ

/-- Boundary-reaching membership implies ordinary local Sobolev membership in the interior.
The converse would discard the bounds near the boundary. -/
theorem MemWkpLocHalf.memWkpLoc_interior (hf : MemWkpLocHalf p U k f) :
    MemWkpLoc p (Opens.interior U) k f := by
  induction k generalizing F with
  | zero => exact memWkpLoc_zero_iff.mpr (hf.mono_set interior_subset)
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact memWkpLoc_succ_iff.mpr ⟨hp.mono_set interior_subset, D, hD, ih hk⟩

/-- An ambient local Sobolev map restricts to the boundary-reaching class on any subset.
Compact sets in the subset are still compact sets of the ambient open domain. -/
theorem MemWkpLoc.restrict_half (hf : MemWkpLoc p Ω k f) (hU : U ⊆ Ω) :
    MemWkpLocHalf p U k f := by
  induction k generalizing F with
  | zero => exact (memWkpLoc_zero_iff.mp hf).mono_set hU
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.mp hf
    exact ⟨hp.mono_set hU, D, hD.mono (interior_subset.trans hU), ih hk⟩

/-- On an open domain the boundary-reaching class agrees with the interior local class. -/
@[simp]
theorem memWkpLocHalf_coe_iff : MemWkpLocHalf p (Ω : Set ℂ) k f ↔ MemWkpLoc p Ω k f := by
  have hΩ : Opens.interior (Ω : Set ℂ) = Ω := Opens.ext Ω.isOpen.interior_eq
  exact ⟨fun hf => hΩ ▸ hf.memWkpLoc_interior, fun hf => hf.restrict_half subset_rfl⟩

/-- Addition preserves boundary-reaching membership. -/
theorem MemWkpLocHalf.add (hf : MemWkpLocHalf p U k f) (hg : MemWkpLocHalf p U k g) :
    MemWkpLocHalf p U k (f + g) := by
  induction k generalizing F with
  | zero => exact hf.add hg
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    obtain ⟨hq, D', hD', hk'⟩ := hg
    exact ⟨hp.add hq, D + D', hD.add hD', ih hk hk'⟩

/-- Negation preserves boundary-reaching membership. -/
theorem MemWkpLocHalf.neg (hf : MemWkpLocHalf p U k f) : MemWkpLocHalf p U k (-f) := by
  induction k generalizing F with
  | zero => exact hf.neg
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.neg, -D, hD.neg, ih hk⟩

/-- Subtraction preserves boundary-reaching membership. -/
theorem MemWkpLocHalf.sub (hf : MemWkpLocHalf p U k f) (hg : MemWkpLocHalf p U k g) :
    MemWkpLocHalf p U k (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Real scalar multiplication preserves boundary-reaching membership. -/
theorem MemWkpLocHalf.const_smul (hf : MemWkpLocHalf p U k f) (c : ℝ) :
    MemWkpLocHalf p U k (c • f) := by
  induction k generalizing F with
  | zero => exact hf.const_smul c
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.const_smul c, c • D, hD.const_smul c, ih hk⟩

/-- Continuous linear maps preserve all boundary-reaching weak derivative orders. -/
theorem MemWkpLocHalf.clm_comp [CompleteSpace G] (hf : MemWkpLocHalf p U k f)
    (A : F →L[ℝ] G) : MemWkpLocHalf p U k (fun z => A (f z)) := by
  induction k generalizing F G with
  | zero => exact hf.clm_comp A
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.clm_comp A, fun z => A.comp (D z), hD.clm_comp A,
      ih hk ((ContinuousLinearMap.compL ℝ ℂ F G) A)⟩

/-- Constant maps have boundary-reaching membership at every order and exponent. -/
@[simp]
theorem memWkpLocHalf_const [CompleteSpace F] (c : F) :
    MemWkpLocHalf p U k (fun _ => c) :=
  (memWkpLoc_const (Ω := ⊤) c).restrict_half (Set.subset_univ U)

/-- The zero map has boundary-reaching membership at every order and exponent. -/
@[simp]
theorem memWkpLocHalf_zero_fun [CompleteSpace F] : MemWkpLocHalf p U k (0 : ℂ → F) :=
  (memWkpLoc_zero_fun (Ω := ⊤)).restrict_half (Set.subset_univ U)

/-- Finite sums preserve boundary-reaching membership. -/
theorem MemWkpLocHalf.sum {ι : Type*} [CompleteSpace F] (s : Finset ι)
    {f : ι → ℂ → F} (hf : ∀ i ∈ s, MemWkpLocHalf p U k (f i)) :
    MemWkpLocHalf p U k (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Pi.zero_def] using
      (memWkpLocHalf_zero_fun (p := p) (U := U) (k := k) (F := F))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end TauCeti

/-- A globally `Cᵏ` map has locally `Lᵖ` weak derivatives up to the boundary of every subset,
for every exponent. In particular the identity and polynomial maps satisfy the half-disc class. -/
theorem ContDiff.memWkpLocHalf {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : ℂ → F} {k : ℕ} {p : ENNReal} {U : Set ℂ}
    (hf : ContDiff ℝ k f) : TauCeti.MemWkpLocHalf p U k f :=
  (hf.contDiffOn.memWkpLoc (Ω := ⊤)).restrict_half (Set.subset_univ U)
