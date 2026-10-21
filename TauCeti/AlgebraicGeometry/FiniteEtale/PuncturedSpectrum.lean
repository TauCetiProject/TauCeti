/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Finite étale covers of a punctured local spectrum

For a local ring, the punctured spectrum is the complement of the closed point. Pullback along
its inclusion restricts finite étale schemes. Purity of the local ring means that this functor is
essentially surjective.

## References

* The Stacks Project, Section 58.20 (Tag 0BM7).
* Ported from Taylor Dupuy, Thomas Tucker and Zhuoran Wang, pcfawd-formalization at commit
  `9a20b3f` (Apache 2.0), `Pcf/Stacks/Purity/PuncturedSpectrum.lean` and
  `Pcf/Stacks/Purity/Hartogs.lean`.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The complement of the closed point in the spectrum of a local ring. -/
@[stacks 0BM7 "the punctured spectrum"]
def puncturedSpectrum : (Spec (.of R)).Opens :=
  -- Opens on an affine scheme are opens of its underlying prime spectrum.
  show TopologicalSpace.Opens (PrimeSpectrum R) from
    { carrier := {IsLocalRing.closedPoint R}ᶜ
      is_open' := (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl }

@[simp]
theorem mem_puncturedSpectrum_iff (x : PrimeSpectrum R) :
    x ∈ puncturedSpectrum R ↔ x ≠ IsLocalRing.closedPoint R := by
  -- `Spec (.of R)` uses `PrimeSpectrum R` as its underlying topological space.
  change x ∉ ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) ↔ _
  simp

theorem closedPoint_notMem_puncturedSpectrum :
    IsLocalRing.closedPoint R ∉ puncturedSpectrum R := by
  simp

/-- Pullback of finite étale schemes along the punctured-spectrum inclusion. -/
noncomputable def restrictPunctured :
    TauCeti.FiniteEtaleScheme (Spec (.of R)) ⥤
      TauCeti.FiniteEtaleScheme (puncturedSpectrum R).toScheme :=
  (TauCeti.finiteEtaleSchemeProperty _).lift
    ((TauCeti.finiteEtaleSchemeProperty _).ι ⋙ Over.pullback (puncturedSpectrum R).ι)
    (fun X ↦ by
      rw [TauCeti.finiteEtaleSchemeProperty_iff]
      -- The over-object map of the pullback is its second projection.
      change IsFinite (Limits.pullback.snd X.obj.hom (puncturedSpectrum R).ι) ∧
        Etale (Limits.pullback.snd X.obj.hom (puncturedSpectrum R).ι)
      exact ⟨inferInstance, inferInstance⟩)

/-- Forgetting finite étaleness identifies restriction with pullback along the puncture. -/
@[simp]
theorem restrictPunctured_comp_ι :
    restrictPunctured R ⋙ (TauCeti.finiteEtaleSchemeProperty _).ι =
      (TauCeti.finiteEtaleSchemeProperty _).ι ⋙ Over.pullback (puncturedSpectrum R).ι :=
  by
    unfold restrictPunctured
    rfl

/-- Purity holds if every finite étale cover of the punctured spectrum extends across the
closed point. -/
@[stacks 0BM7 "definition of purity"]
def PurityHolds : Prop := (restrictPunctured R).EssSurj

/-- Under purity, every finite étale cover of the puncture extends across the closed point. -/
theorem PurityHolds.exists_extension (h : PurityHolds R)
    (cover : TauCeti.FiniteEtaleScheme (puncturedSpectrum R).toScheme) :
    ∃ extension : TauCeti.FiniteEtaleScheme (Spec (.of R)),
      Nonempty ((restrictPunctured R).obj extension ≅ cover) := by
  let : (restrictPunctured R).EssSurj := h
  exact Functor.EssSurj.mem_essImage (restrictPunctured R) cover

/-- The punctured spectrum is the union of basic opens when their generators have maximal
radical. -/
theorem puncturedSpectrum_eq_iSup_basicOpen {s : Set R}
    (hs : (Ideal.span s).radical = IsLocalRing.maximalIdeal R) :
    puncturedSpectrum R = ⨆ x : s, PrimeSpectrum.basicOpen x.1 := by
  -- Opens on `Spec (.of R)` are opens of its underlying `PrimeSpectrum R`.
  change (show TopologicalSpace.Opens (PrimeSpectrum R) from puncturedSpectrum R) =
    ⨆ x : s, PrimeSpectrum.basicOpen x.1
  apply SetLike.ext'
  rw [TopologicalSpace.Opens.coe_iSup]
  ext p
  simp only [Set.mem_iUnion, SetLike.mem_coe, puncturedSpectrum,
    PrimeSpectrum.mem_basicOpen]
  constructor
  · intro hp
    by_contra h
    push Not at h
    have hs_le : s ⊆ p.asIdeal := fun x hx ↦ h ⟨x, hx⟩
    have hm_le : IsLocalRing.maximalIdeal R ≤ p.asIdeal := by
      rw [← hs]
      exact p.isPrime.radical_le_iff.mpr (Ideal.span_le.mpr hs_le)
    have hp_le : p.asIdeal ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal p.isPrime.ne_top
    apply hp
    apply PrimeSpectrum.ext
    exact le_antisymm hp_le hm_le
  · rintro ⟨x, hx⟩ hp
    have hxm : x.1 ∈ IsLocalRing.maximalIdeal R := by
      rw [← hs]
      exact Ideal.le_radical (Ideal.subset_span x.2)
    apply hx
    rw [hp]
    exact hxm

/-- The punctured spectrum of a Noetherian local ring is quasi-compact. -/
theorem isCompact_puncturedSpectrum [IsNoetherianRing R] :
    IsCompact (puncturedSpectrum R).1 :=
  NoetherianSpace.isCompact _

end IsLocalRing
