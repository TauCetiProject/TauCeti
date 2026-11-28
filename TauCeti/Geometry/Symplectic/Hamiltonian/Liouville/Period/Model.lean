/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Section
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LatticeQuotient.ActionAngle
import Mathlib.Algebra.Group.Subgroup.Finsupp

/-!
# A regular Lagrangian torus fibration with a Lagrangian section is its model `T*B/Λ`

Let `σ` be a symplectic form on a boundaryless manifold `M` and let `π : M → B` be a regular
Lagrangian torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
with period lattice `Λ_b ⊆ T*_b B` (`IsLagrangianTorusFibration.periodLattice`). Suppose that the
period lattice is spanned at every point by a global frame `α_1, …, α_n` of one-forms on `B`:

`Λ_b = ℤ α_1(b) + ⋯ + ℤ α_n(b)` for every `b ∈ B`.

Then the quotient `T*B/Λ` (`TauCeti.CotangentBundle.LatticeQuotient α hα`) is defined, and this
file identifies `M` with it. Every smooth section `s` of `π` has a section map `Φ_s : T*B → M`,
`Φ_s(ξ) = (-ξ) • s(b)` (`IsLagrangianTorusFibration.sectionMap`), whose fibres are exactly the
cosets of `Λ`. So it descends to a bijection `T*B/Λ → M`
(`IsLagrangianTorusFibration.quotientSectionMap`), which is a local diffeomorphism because `Φ_s`
and the quotient map are. It is therefore a diffeomorphism over `B`
(`IsLagrangianTorusFibration.sectionDiffeomorph`).

The translations of `T*B` by the forms `α_i` preserve `Φ_s`, hence the pullback
`Φ_s^* σ = ω + π^* (s^* σ)`, and so they preserve the canonical form `ω = -dλ`. A translation by a
one-form preserves `ω` exactly when the form is closed, so **the frame `α` is closed**
(`IsLagrangianTorusFibration.isClosed_of_periodLattice_eq`), and `T*B/Λ` carries the symplectic
form descended from `ω` (`TauCeti.CotangentBundle.LatticeQuotient.symplecticForm`). The
diffeomorphism pulls `σ` back to that form plus `π^* (s^* σ)`
(`IsLagrangianTorusFibration.mpullback_sectionDiffeomorph`). Hence:

* **A Lagrangian section trivializes the fibration symplectically.** If `s^* σ = 0`, the
  diffeomorphism `T*B/Λ ≃ M` over `B` is a symplectomorphism
  (`IsLagrangianTorusFibration.mpullback_sectionDiffeomorph_eq_symplecticForm`). Conversely the
  zero section of `T*B/Λ` is Lagrangian, so `π` has a smooth Lagrangian section exactly when
  there is a symplectomorphism `T*B/Λ ≃ M` over `B`
  (`IsLagrangianTorusFibration.exists_lagrangian_section_iff`). This is the comparison of a
  regular Lagrangian torus fibration with its model in the case of a globally framed period
  lattice.
* **Action–angle coordinates.** If moreover the frame is exact, `α_i = p • da_i` for a smooth
  developing map `a : B → ℝⁿ` and a period `p > 0`, then composing the inverse of the
  diffeomorphism with the action–angle chart of `T*B/Λ`
  (`TauCeti.CotangentBundle.LatticeQuotient.actionAngleChart`) gives a symplectic local
  diffeomorphism from `M` into the cotangent bundle of the torus `(ℝ/pℤ)ⁿ` whose actions are
  `a ∘ π` and which is injective on every fibre of `π`
  (`IsLagrangianTorusFibration.exists_actionAngle_of_lagrangian_section`). It is injective
  exactly when `a` is, and then its image is open, the covectors with actions in `a(B)`, and on
  it `σ = ∑ j, dθ_j ∧ dI_j`. This is the sufficiency half of Duistermaat's criterion for
  action–angle coordinates: trivial monodromy and exact period forms, together with a Lagrangian
  section, and for global coordinates into `T*Tⁿ` an injective developing map.

## Main definitions

* `IsLagrangianTorusFibration.quotientSectionMap`: the map `T*B/Λ → M` induced by the section
  map of a section.
* `IsLagrangianTorusFibration.sectionDiffeomorph`: for a smooth section, this map as a
  diffeomorphism.

## Main results

* `IsLagrangianTorusFibration.quotientSectionMap_mk`,
  `IsLagrangianTorusFibration.proj_quotientSectionMap`: the induced map lifts the section map and
  lies over `B`.
* `IsLagrangianTorusFibration.bijective_quotientSectionMap`,
  `IsLagrangianTorusFibration.isLocalDiffeomorph_quotientSectionMap`: it is a bijective local
  diffeomorphism.
* `IsLagrangianTorusFibration.isClosed_of_periodLattice_eq`: a frame spanning the period lattice
  of a fibration with a smooth section consists of closed one-forms.
* `IsLagrangianTorusFibration.mpullback_sectionDiffeomorph`,
  `IsLagrangianTorusFibration.mpullback_sectionDiffeomorph_eq_symplecticForm`: the
  diffeomorphism pulls `σ` back to the model form plus `π^* (s^* σ)`, and to the model form for a
  Lagrangian section.
* `IsLagrangianTorusFibration.exists_lagrangian_section_iff`: `π` has a smooth Lagrangian section
  exactly when it is symplectomorphic over `B` to its model `T*B/Λ`.
* `IsLagrangianTorusFibration.exists_actionAngle_of_lagrangian_section`: action–angle
  coordinates from a Lagrangian section and an exact frame, global when the developing map is
  injective.

All in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Sections 1 and 2 (the identification of a fibration with a Lagrangian section with
  `T*B / Λ`, and the obstructions to global action–angle coordinates).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.
-/

public section

noncomputable section

open Bundle (TotalSpace)
open Function Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

open CotangentBundle CotangentBundle.LatticeQuotient CotangentBundle.LatticeCover

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}
  {ι : Type*} [Fintype ι] {α : ι → SmoothForm J B ℝ 1}

variable (h : hσ.IsLagrangianTorusFibration J π) (hσc : σ.IsClosed) {s : B → M}
  (hs : ∀ b, π (s b) = b)
  (hα : IsLocalFrameOn J (F →L[ℝ] ℝ) ∞ (fun i x ↦ SmoothForm.degreeOneEquiv (α i) x) univ)
  (hΛ : ∀ b, h.periodLattice hσc b =
    AddSubgroup.closure (range fun i ↦ (SmoothForm.degreeOneEquiv (α i) b : F →L[ℝ] ℝ)))

/-! ### The section map on `T*B/Λ` -/

omit [Fintype ι] in
include hΛ in
/-- Each covector `α i b` of the frame is a period. -/
theorem degreeOneEquiv_mem_periodLattice (i : ι) (b : B) :
    (SmoothForm.degreeOneEquiv (α i) b : F →L[ℝ] ℝ) ∈ h.periodLattice hσc b := by
  rw [hΛ]
  exact AddSubgroup.subset_closure ⟨i, rfl⟩

include hΛ in
/-- An integer combination of the covectors `α i b` of the frame is a period. -/
theorem sum_smul_degreeOneEquiv_mem_periodLattice (b : B) (k : ι → ℤ) :
    (∑ i, (k i : ℝ) • SmoothForm.degreeOneEquiv (α i) b : F →L[ℝ] ℝ) ∈
      h.periodLattice hσc b := by
  refine AddSubgroup.sum_mem _ fun i _ ↦ ?_
  rw [Int.cast_smul_eq_zsmul]
  exact AddSubgroup.zsmul_mem _ (h.degreeOneEquiv_mem_periodLattice hσc hΛ i b) _

include hΛ in
/-- **The section map on `T*B/Λ`.** When the period lattice is spanned at every point by the
frame `α`, the section map `Φ_s : T*B → M` of a section `s` is constant on the orbits of the
lattice translations, and so descends to the quotient `T*B/Λ`. -/
def quotientSectionMap : LatticeQuotient α hα → M :=
  MulAction.orbitRelQuotientLift (G := Multiplicative (ι → ℤ))
    (fun z ↦ h.sectionMap hσc hs ((ofCotangent hα).symm z)) fun k z ↦ by
      obtain ⟨z, rfl⟩ := (ofCotangent hα).surjective z
      rw [smul_ofCotangent, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact h.sectionMap_mk_add_of_mem hσc hs z.proj z.snd _
        (h.sum_smul_degreeOneEquiv_mem_periodLattice hσc hΛ z.proj k.toAdd)

/-- The map induced on `T*B/Λ` by the section map sends the class of a covector to the image of
that covector under the section map. -/
@[simp]
theorem quotientSectionMap_mk (z : CotangentBundle J B) :
    h.quotientSectionMap hσc hs hα hΛ (LatticeQuotient.mk hα z) = h.sectionMap hσc hs z := by
  rw [quotientSectionMap, mk_def, MulAction.orbitRelQuotientLift_mk, Equiv.symm_apply_apply]

/-- The map induced on `T*B/Λ` by the section map lifts the section map along the quotient
map. -/
theorem quotientSectionMap_comp_mk :
    h.quotientSectionMap hσc hs hα hΛ ∘ LatticeQuotient.mk hα = h.sectionMap hσc hs :=
  funext (h.quotientSectionMap_mk hσc hs hα hΛ)

/-- **The map induced by the section map lies over the base**: its composite with `π` is the
projection `T*B/Λ → B`. -/
theorem proj_quotientSectionMap (z : LatticeQuotient α hα) :
    π (h.quotientSectionMap hσc hs hα hΛ z) = LatticeQuotient.proj hα z := by
  obtain ⟨z, rfl⟩ := LatticeQuotient.mk_surjective hα z
  rw [quotientSectionMap_mk, h.proj_sectionMap hσc hs, proj_mk]

/-- The map induced on `T*B/Λ` by the section map is injective: two covectors with the same image
lie over the same point and differ by a period, that is by an integer combination of the
frame. -/
theorem injective_quotientSectionMap : Injective (h.quotientSectionMap hσc hs hα hΛ) := by
  intro z w hzw
  obtain ⟨⟨b, ξ⟩, rfl⟩ := LatticeQuotient.mk_surjective hα z
  obtain ⟨⟨b', η⟩, rfl⟩ := LatticeQuotient.mk_surjective hα w
  rw [quotientSectionMap_mk, quotientSectionMap_mk] at hzw
  obtain rfl : b = b' := by
    simpa only [proj_sectionMap] using congrArg π hzw
  have hmem := (h.sectionMap_mk_eq_sectionMap_mk_iff hσc hs b ξ η).1 hzw
  rw [hΛ] at hmem
  obtain ⟨k, hk⟩ := AddSubgroup.mem_closure_range_iff_of_fintype.1 hmem
  refine (mk_mk_eq_mk_mk_iff hα).2 ⟨k, ?_⟩
  simp only [Int.cast_smul_eq_zsmul]
  exact eq_add_of_sub_eq' hk

/-- The map induced on `T*B/Λ` by the section map is surjective, since the section map is. -/
theorem surjective_quotientSectionMap : Surjective (h.quotientSectionMap hσc hs hα hΛ) := by
  rw [← (LatticeQuotient.mk_surjective hα).of_comp_iff, quotientSectionMap_comp_mk]
  exact h.surjective_sectionMap hσc hs

/-- The map induced on `T*B/Λ` by the section map is a bijection onto `M`. -/
theorem bijective_quotientSectionMap : Bijective (h.quotientSectionMap hσc hs hα hΛ) :=
  ⟨h.injective_quotientSectionMap hσc hs hα hΛ, h.surjective_quotientSectionMap hσc hs hα hΛ⟩

variable [BoundarylessManifold J B]

/-- **For a smooth section, the induced map is a local diffeomorphism** `T*B/Λ → M`: its composite
with the quotient map, a local diffeomorphism, is the section map, which is one. -/
theorem isLocalDiffeomorph_quotientSectionMap (hsm : ContMDiff J I ∞ s) :
    IsLocalDiffeomorph (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) I ∞ (h.quotientSectionMap hσc hs hα hΛ) := by
  intro y
  obtain ⟨z, rfl⟩ := LatticeQuotient.mk_surjective hα y
  refine IsLocalDiffeomorphAt.of_comp_right ?_ (LatticeQuotient.isLocalDiffeomorph_mk hα z)
  rw [quotientSectionMap_comp_mk]
  exact h.isLocalDiffeomorph_sectionMap hσc hs hsm z

/-- **The diffeomorphism `T*B/Λ ≃ M` defined by a smooth section** `s` of a regular Lagrangian
torus fibration whose period lattice is spanned by the frame `α`: the class of a covector `ξ` at
`b` goes to `(-ξ) • s(b)`. It lies over `B` (`proj_sectionDiffeomorph`). -/
def sectionDiffeomorph (hsm : ContMDiff J I ∞ s) :
    LatticeQuotient α hα ≃ₘ⟮J.prod 𝓘(ℝ, F →L[ℝ] ℝ), I⟯ M :=
  (h.isLocalDiffeomorph_quotientSectionMap hσc hs hα hΛ hsm).diffeomorphOfBijective
    (h.bijective_quotientSectionMap hσc hs hα hΛ)

/-- The diffeomorphism defined by a smooth section is the map induced by its section map. -/
@[simp]
theorem coe_sectionDiffeomorph (hsm : ContMDiff J I ∞ s) :
    ⇑(h.sectionDiffeomorph hσc hs hα hΛ hsm) = h.quotientSectionMap hσc hs hα hΛ :=
  IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

/-- **The diffeomorphism defined by a smooth section lies over the base.** -/
theorem proj_sectionDiffeomorph (hsm : ContMDiff J I ∞ s) (z : LatticeQuotient α hα) :
    π (h.sectionDiffeomorph hσc hs hα hΛ hsm z) = LatticeQuotient.proj hα z := by
  rw [coe_sectionDiffeomorph, h.proj_quotientSectionMap hσc hs hα hΛ]

/-! ### The frame is closed, and the pullback of the symplectic form -/

omit [Fintype ι] in
include hs hΛ in
/-- **A frame spanning the period lattice is closed.** If the period lattice of a regular
Lagrangian torus fibration with a smooth section is spanned at every point by the frame `α`, then
every `α i` is a closed one-form. Translation of `T*B` by `α i` preserves the section map, which
pulls `σ` back to `ω + π^* (s^* σ)`; it preserves `π^* (s^* σ)` as it lies over `B`, so it preserves
the canonical form `ω`, which happens exactly when `α i` is closed. -/
theorem isClosed_of_periodLattice_eq (hsm : ContMDiff J I ∞ s) (i : ι) : (α i).IsClosed := by
  set T := vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv (α i))
    (SmoothForm.degreeOneEquiv (α i)).contMDiff
  have hT : h.sectionMap hσc hs ∘ T = h.sectionMap hσc hs := by
    funext ⟨b, ξ⟩
    rw [comp_apply, vectorBundleTranslateDiffeomorph_apply]
    exact h.sectionMap_mk_add_of_mem hσc hs b ξ _ (h.degreeOneEquiv_mem_periodLattice hσc hΛ i b)
  have hproj : (TotalSpace.proj : CotangentBundle J B → B) ∘ T = TotalSpace.proj :=
    funext fun _ ↦ by rw [comp_apply, vectorBundleTranslateDiffeomorph_apply]
  have hpull := congrArg (SmoothForm.mpullback T T.contMDiff)
    (h.mpullback_sectionMap hσc hs hsm)
  rw [SmoothForm.mpullback_mpullback, map_add, SmoothForm.mpullback_mpullback] at hpull
  simp only [hT, hproj, h.mpullback_sectionMap hσc hs hsm, add_left_inj] at hpull
  exact (mpullback_vectorBundleTranslateDiffeomorph_symplecticForm_eq_self_iff (α i)).1 hpull.symm

/-- **The pullback of the symplectic form along the diffeomorphism of a smooth section** is the
symplectic form of `T*B/Λ` plus the pullback of `s^* σ` along the projection `T*B/Λ → B`. -/
theorem mpullback_sectionDiffeomorph (hsm : ContMDiff J I ∞ s) :
    SmoothForm.mpullback (h.sectionDiffeomorph hσc hs hα hΛ hsm)
        (h.sectionDiffeomorph hσc hs hα hΛ hsm).contMDiff σ =
      LatticeQuotient.symplecticForm hα (h.isClosed_of_periodLattice_eq hσc hs hΛ hsm) +
        SmoothForm.mpullback (LatticeQuotient.proj hα) (LatticeQuotient.contMDiff_proj hα)
          (SmoothForm.mpullback s hsm σ) := by
  refine SmoothForm.mpullback_injective_of_surjective (LatticeQuotient.contMDiff_mk hα)
    (LatticeQuotient.mk_surjective hα) (fun z ↦
      ((LatticeQuotient.isLocalDiffeomorph_mk hα).isInvertible_mfderiv (by simp) z).surjective) ?_
  rw [SmoothForm.mpullback_mpullback, map_add, mpullback_mk_symplecticForm,
    SmoothForm.mpullback_mpullback]
  simp only [coe_sectionDiffeomorph, quotientSectionMap_comp_mk, proj_comp_mk]
  exact h.mpullback_sectionMap hσc hs hsm

/-- **A Lagrangian section identifies the fibration with its model.** If `s` is a smooth
Lagrangian section, `s^* σ = 0`, the diffeomorphism `T*B/Λ ≃ M` it defines over `B` pulls `σ`
back to the symplectic form of `T*B/Λ` descended from the canonical form `ω = -dλ`. -/
theorem mpullback_sectionDiffeomorph_eq_symplecticForm (hsm : ContMDiff J I ∞ s)
    (hsσ : SmoothForm.mpullback s hsm σ = 0) :
    SmoothForm.mpullback (h.sectionDiffeomorph hσc hs hα hΛ hsm)
        (h.sectionDiffeomorph hσc hs hα hΛ hsm).contMDiff σ =
      LatticeQuotient.symplecticForm hα (h.isClosed_of_periodLattice_eq hσc hs hΛ hsm) := by
  rw [mpullback_sectionDiffeomorph, hsσ, map_zero, add_zero]

include hΛ in
/-- **Lagrangian sections and the model `T*B/Λ`.** For a regular Lagrangian torus fibration whose
period lattice is spanned at every point by a closed frame `α`, the projection `π` has a smooth
Lagrangian section exactly when there is a diffeomorphism `T*B/Λ ≃ M` over `B` pulling `σ` back to
the symplectic form of `T*B/Λ`. Closedness of `α` is automatic as soon as `π` has a smooth section
(`isClosed_of_periodLattice_eq`). -/
theorem exists_lagrangian_section_iff (hclosed : ∀ i, (α i).IsClosed) :
    (∃ (s : B → M) (hsm : ContMDiff J I ∞ s), (∀ b, π (s b) = b) ∧
        SmoothForm.mpullback s hsm σ = 0) ↔
      ∃ Ψ : LatticeQuotient α hα ≃ₘ⟮J.prod 𝓘(ℝ, F →L[ℝ] ℝ), I⟯ M,
        (∀ z, π (Ψ z) = LatticeQuotient.proj hα z) ∧
          SmoothForm.mpullback Ψ Ψ.contMDiff σ = LatticeQuotient.symplecticForm hα hclosed := by
  constructor
  · rintro ⟨s, hsm, hs, hsσ⟩
    exact ⟨h.sectionDiffeomorph hσc hs hα hΛ hsm, h.proj_sectionDiffeomorph hσc hs hα hΛ hsm,
      h.mpullback_sectionDiffeomorph_eq_symplecticForm hσc hs hα hΛ hsm hsσ⟩
  · rintro ⟨Ψ, hΨπ, hΨσ⟩
    -- The image under `Ψ` of the zero section of `T*B/Λ` is a Lagrangian section of `π`.
    set z₀ : B → LatticeQuotient α hα := fun x ↦
      LatticeQuotient.mk hα (TotalSpace.mk' (F →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv 0 x))
    have hz : ContMDiff J (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ z₀ :=
      (LatticeQuotient.contMDiff_mk hα).comp
        (SmoothForm.degreeOneEquiv (0 : SmoothForm J B ℝ 1)).contMDiff
    refine ⟨Ψ ∘ z₀, Ψ.contMDiff.comp hz, fun b ↦ by rw [comp_apply, hΨπ, proj_mk], ?_⟩
    rw [← SmoothForm.mpullback_mpullback _ _ hz Ψ.contMDiff, hΨσ,
      mpullback_mk_comp_section_symplecticForm, map_zero, neg_zero]

/-! ### Global action–angle coordinates -/

variable [DecidableEq ι] (p : ℝ) [Fact (0 < p)] {a : B → ι → ℝ}

include hs hα hΛ in
/-- **Action–angle coordinates from a Lagrangian section.** Let the period lattice of a regular
Lagrangian torus fibration be spanned at every point by the exact frame `α_i = p • da_i` of a
smooth developing map `a : B → ℝ^ι`, and let `π` have a smooth Lagrangian section `s`. Then there
is a local diffeomorphism `Φ` from `M` into the cotangent bundle of the torus `ι → AddCircle p`
which pulls the canonical form back to `σ`, whose actions are `a ∘ π`, which is injective on every
fibre of `π`, and whose image is the set of covectors with actions in `a(B)`. It is injective
exactly when `a` is; then `Φ` is a symplectomorphism of `M` onto this open set of covectors, on
which `σ = ∑ j, dθ_j ∧ dI_j` and `π` reads `I = a`. The map is the inverse of
`sectionDiffeomorph` followed by the action–angle chart of `T*B/Λ`. -/
theorem exists_actionAngle_of_lagrangian_section (hsm : ContMDiff J I ∞ s)
    (hsσ : SmoothForm.mpullback s hsm σ = 0) (ha : ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ a)
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv J 𝓘(ℝ, ι → ℝ) a x v i) :
    ∃ (Φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
      (hΦ : IsLocalDiffeomorph I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
        𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ),
      (∀ b, InjOn Φ (π ⁻¹' {b})) ∧ (Injective Φ ↔ Injective a) ∧
        SmoothForm.mpullback Φ hΦ.contMDiff
            (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
              (ι → AddCircle p)) = σ ∧
        (∀ y, torusActions p (Φ y) = a (π y)) ∧
        range Φ = {z | torusActions p z ∈ range a} := by
  set Ψ := h.sectionDiffeomorph hσc hs hα hΛ hsm
  have hΦ : IsLocalDiffeomorph I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ (actionAngleChart hα p a ∘ Ψ.symm) := fun y ↦
    IsLocalDiffeomorphAt.comp (hf := Ψ.symm.isLocalDiffeomorph y)
      (hg := isLocalDiffeomorph_actionAngleChart hα ha hαa _)
  -- `Ψ⁻¹` maps the fibre of `π` over `b` into the fibre of `T*B/Λ` over `b`.
  have hΨπ (y : M) : LatticeQuotient.proj hα (Ψ.symm y) = π y := by
    rw [← h.proj_sectionDiffeomorph hσc hs hα hΛ hsm, Diffeomorph.apply_symm_apply]
  refine ⟨actionAngleChart hα p a ∘ Ψ.symm, hΦ, fun b y hy y' hy' hyy' ↦ ?_,
    ((Injective.of_comp_iff' _ Ψ.symm.bijective).trans (actionAngleChart_injective_iff hα)), ?_,
    fun y ↦ ?_, ?_⟩
  · exact Ψ.symm.injective
      (injOn_actionAngleChart hα b ((hΨπ y).trans hy) ((hΨπ y').trans hy') hyy')
  · rw [← SmoothForm.mpullback_mpullback _ _ Ψ.symm.contMDiff
      (contMDiff_actionAngleChart hα ha hαa), mpullback_actionAngleChart_symplecticForm hα ha hαa]
    exact SmoothForm.mpullback_symm_eq_of_mpullback_eq
      (h.mpullback_sectionDiffeomorph_eq_symplecticForm hσc hs hα hΛ hsm hsσ)
  · rw [comp_apply, torusActions_actionAngleChart, hΨπ]
  · exact (Ψ.symm.surjective.range_comp _).trans (range_actionAngleChart hα)

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration
