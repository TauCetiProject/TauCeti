/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Radial.Basic

/-!
# Open annuli and open discs in the adic spectrum

Given families `a, b : ℕ → A` of radius representatives, the open annulus and the open disc are
the increasing unions of closed radial regions

```text
𝔸°(A⁺, T, a, b) = ⋃ⱼ 𝔸(A⁺, T, aⱼ, bⱼ),      𝔻°(A⁺, T, b) = ⋃ⱼ 𝔻(A⁺, T, bⱼ).
```

Over a complete nontrivially valued field `C`, in an ambient disc `Spa (C⟨T / c⟩)` with `|c| ≥ R`,
and with `|aⱼ| > r` decreasing to `r` and `|bⱼ| < R` increasing to `R`, these are the analytic
open annulus `r < |T| < R` and the analytic open disc `|T| < R`: Berkovich's `B(r, R)` and
`D(0, R)`.

They are not the strict valuative loci `{v(a) < v(T) < v(b)}` and `{v(T) < v(b)}` at the
endpoints. Ito's rank-two point `η(R)` satisfies `v(T) < R` yet lies in no closed disc of radius
smaller than `R`, so it lies in the strict locus but not in the union. This is why the open
regions are defined as unions of closed ones. The unions depend on the families only up to
mutual cofinality (`openAnnulus_eq_openAnnulus`, `openDisc_eq_openDisc`). A constant family gives
back the closed region (`openAnnulus_const`, `openDisc_const`), so the analytic openness of the
union needs hypotheses on the families; none are imposed here.

## Main results

* `TauCeti.ValuationSpectrum.mem_openAnnulus_iff` and `TauCeti.ValuationSpectrum.mem_openDisc_iff`:
  membership means membership in one closed stage.
* `TauCeti.ValuationSpectrum.openAnnulus_eq_openAnnulus` and
  `TauCeti.ValuationSpectrum.openDisc_eq_openDisc`: mutually cofinal families of radii define the
  same open region.
* `TauCeti.ValuationSpectrum.openAnnulus_eq_iUnion_inter_rationalSubset` and
  `TauCeti.ValuationSpectrum.openDisc_eq_iUnion_rationalSubset`: the open regions are unions of
  (intersections of) rational subsets. Open annuli are therefore always relatively open in
  `Spa (A, A⁺)`, and open discs are when the radii are units.
* `TauCeti.ValuationSpectrum.comap_preimage_openAnnulus_inter_spa` and
  `TauCeti.ValuationSpectrum.comap_preimage_openDisc_inter_spa`: compatibility with pulling back
  along continuous plus-preserving ring maps.

## References

* K. Ito, *Uniform local constancy of étale cohomology of rigid analytic varieties*, §6.2,
  pp. 37–38 (before and in the proof of Lemma 6.12), and Appendix A.1, Example A.1 (2).
* V. G. Berkovich, *Étale cohomology for non-Archimedean analytic spaces*, §6.3,
  Remarks 6.3.4 (i) and Corollary 6.3.6.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-! ### Open annuli -/

/-- **The open annulus `𝔸°(A⁺, T, a, b)`** attached to families `a, b : ℕ → A` of inner and outer
radius representatives: the union of the closed annuli `𝔸(A⁺, T, aⱼ, bⱼ)`. With `|aⱼ| > r`
decreasing to `r` and `|bⱼ| < R` increasing to `R` over a complete nontrivially valued field, this
is the analytic open annulus `r < |T| < R`. -/
def openAnnulus (Aplus : Subring A) (T : A) (a b : ℕ → A) : Set (Spv A) :=
  ⋃ j, closedAnnulus Aplus T (a j) (b j)

/-- The set-level characterization of the open annulus. -/
theorem openAnnulus_def (Aplus : Subring A) (T : A) (a b : ℕ → A) :
    openAnnulus Aplus T a b = ⋃ j, closedAnnulus Aplus T (a j) (b j) := (rfl)

/-- Membership in `𝔸°(A⁺, T, a, b)` is membership in one closed-annulus stage. -/
@[simp]
theorem mem_openAnnulus_iff (Aplus : Subring A) (T : A) (a b : ℕ → A) (v : Spv A) :
    v ∈ openAnnulus Aplus T a b ↔ ∃ j, v ∈ closedAnnulus Aplus T (a j) (b j) :=
  Set.mem_iUnion

/-- Every closed-annulus stage lies in the open annulus. -/
theorem closedAnnulus_subset_openAnnulus (Aplus : Subring A) (T : A) (a b : ℕ → A) (j : ℕ) :
    closedAnnulus Aplus T (a j) (b j) ⊆ openAnnulus Aplus T a b :=
  Set.subset_iUnion (fun j ↦ closedAnnulus Aplus T (a j) (b j)) j

/-- Every open annulus lies in the adic spectrum. -/
theorem openAnnulus_subset_spa (Aplus : Subring A) (T : A) (a b : ℕ → A) :
    openAnnulus Aplus T a b ⊆ spa Aplus :=
  Set.iUnion_subset fun j ↦ closedAnnulus_subset_spa Aplus T (a j) (b j)

/-- Every open annulus lies in the punctured disc of any outer radius `b'` dominating all the
outer radii `bⱼ` at every point of `Spa (A, A⁺)`. -/
theorem openAnnulus_subset_puncturedClosedDisc (Aplus : Subring A) (T : A) (a b : ℕ → A)
    {b' : A} (hb : ∀ j, ∀ v ∈ spa Aplus, v.toValuativeRel.vle (b j) b') :
    openAnnulus Aplus T a b ⊆ puncturedClosedDisc Aplus T b' :=
  Set.iUnion_subset fun j ↦
    (closedAnnulus_subset_closedAnnulus Aplus T (fun v _ ↦ v.toValuativeRel.vle_refl _)
      (hb j)).trans (closedAnnulus_subset_puncturedClosedDisc Aplus T (a j) b')

/-- **Constant radius families give the closed annulus**, not a strict one. -/
@[simp]
theorem openAnnulus_const (Aplus : Subring A) (T a b : A) :
    openAnnulus Aplus T (fun _ ↦ a) (fun _ ↦ b) = closedAnnulus Aplus T a b :=
  Set.iUnion_const _

/-- **Comparing open annuli.** If every closed stage of `(a, b)` lies inside a stage of
`(a', b')`, with the inner radii compared downwards and the outer radii upwards at every point of
`Spa (A, A⁺)`, then `𝔸°(A⁺, T, a, b) ⊆ 𝔸°(A⁺, T, a', b')`. -/
theorem openAnnulus_subset_openAnnulus (Aplus : Subring A) (T : A) {a b a' b' : ℕ → A}
    (h : ∀ j, ∃ k, ∀ v ∈ spa Aplus,
      v.toValuativeRel.vle (a' k) (a j) ∧ v.toValuativeRel.vle (b j) (b' k)) :
    openAnnulus Aplus T a b ⊆ openAnnulus Aplus T a' b' :=
  Set.iUnion_subset fun j ↦ by
    obtain ⟨k, hk⟩ := h j
    exact (closedAnnulus_subset_closedAnnulus Aplus T (fun v hv ↦ (hk v hv).1)
      (fun v hv ↦ (hk v hv).2)).trans (closedAnnulus_subset_openAnnulus Aplus T a' b' k)

/-- **Mutually cofinal radius families define the same open annulus.** -/
theorem openAnnulus_eq_openAnnulus (Aplus : Subring A) (T : A) {a b a' b' : ℕ → A}
    (h : ∀ j, ∃ k, ∀ v ∈ spa Aplus,
      v.toValuativeRel.vle (a' k) (a j) ∧ v.toValuativeRel.vle (b j) (b' k))
    (h' : ∀ k, ∃ j, ∀ v ∈ spa Aplus,
      v.toValuativeRel.vle (a j) (a' k) ∧ v.toValuativeRel.vle (b' k) (b j)) :
    openAnnulus Aplus T a b = openAnnulus Aplus T a' b' :=
  (openAnnulus_subset_openAnnulus Aplus T h).antisymm (openAnnulus_subset_openAnnulus Aplus T h')

/-- **The open annulus is a union of intersections of rational subsets**:
`𝔸°(A⁺, T, a, b) = ⋃ⱼ R({T} / bⱼ) ∩ R({aⱼ} / T)`, for arbitrary radius families. -/
theorem openAnnulus_eq_iUnion_inter_rationalSubset (Aplus : Subring A) (T : A) (a b : ℕ → A) :
    openAnnulus Aplus T a b =
      ⋃ j, rationalSubset Aplus {T} (b j) ∩ rationalSubset Aplus {a j} T := by
  simp only [openAnnulus_def, closedAnnulus_eq_inter_rationalSubset]

/-- **Open annuli are relatively open** in `Spa (A, A⁺)`; no hypothesis on the radii is needed,
since each closed stage is relatively open. -/
theorem isOpen_val_preimage_openAnnulus (Aplus : Subring A) (T : A) (a b : ℕ → A) :
    IsOpen (Subtype.val ⁻¹' openAnnulus Aplus T a b : Set (spa Aplus)) := by
  rw [openAnnulus_def, Set.preimage_iUnion]
  exact isOpen_iUnion fun j ↦ isOpen_val_preimage_closedAnnulus Aplus T (a j) (b j)

/-- **Pulling back an open annulus.** For a continuous ring map `φ : A → B` carrying `A⁺` into
`B⁺`, the points of `Spa (B, B⁺)` whose pullback lies in `𝔸°(A⁺, T, a, b)` form
`𝔸°(B⁺, φ T, φ ∘ a, φ ∘ b)`. -/
theorem comap_preimage_openAnnulus_inter_spa {B : Type*} [CommRing B] [TopologicalSpace B]
    {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (T : A) (a b : ℕ → A) :
    comap φ ⁻¹' openAnnulus Aplus T a b ∩ spa Bplus =
      openAnnulus Bplus (φ T) (φ ∘ a) (φ ∘ b) := by
  simp only [openAnnulus_def, Set.preimage_iUnion, Set.iUnion_inter, Function.comp_apply,
    comap_preimage_closedAnnulus_inter_spa hφ hplus]

/-- The open annulus with coordinate `0` is empty. -/
@[simp]
theorem openAnnulus_zero_left (Aplus : Subring A) (a b : ℕ → A) :
    openAnnulus Aplus 0 a b = ∅ := by
  simp [openAnnulus_def]

/-! ### Open discs -/

/-- **The open disc `𝔻°(A⁺, T, b)`** attached to a family `b : ℕ → A` of radius
representatives: the union of the closed discs `𝔻(A⁺, T, bⱼ)`. With `|bⱼ| < R` increasing to
`R` over a complete nontrivially valued field, this is the analytic open disc `|T| < R`. -/
def openDisc (Aplus : Subring A) (T : A) (b : ℕ → A) : Set (Spv A) :=
  ⋃ j, closedDisc Aplus T (b j)

/-- The set-level characterization of the open disc. -/
theorem openDisc_def (Aplus : Subring A) (T : A) (b : ℕ → A) :
    openDisc Aplus T b = ⋃ j, closedDisc Aplus T (b j) := (rfl)

/-- Membership in `𝔻°(A⁺, T, b)` is membership in one closed-disc stage. -/
@[simp]
theorem mem_openDisc_iff (Aplus : Subring A) (T : A) (b : ℕ → A) (v : Spv A) :
    v ∈ openDisc Aplus T b ↔ ∃ j, v ∈ closedDisc Aplus T (b j) :=
  Set.mem_iUnion

/-- Every closed-disc stage lies in the open disc. -/
theorem closedDisc_subset_openDisc (Aplus : Subring A) (T : A) (b : ℕ → A) (j : ℕ) :
    closedDisc Aplus T (b j) ⊆ openDisc Aplus T b :=
  Set.subset_iUnion (fun j ↦ closedDisc Aplus T (b j)) j

/-- Every open disc lies in the adic spectrum. -/
theorem openDisc_subset_spa (Aplus : Subring A) (T : A) (b : ℕ → A) :
    openDisc Aplus T b ⊆ spa Aplus :=
  Set.iUnion_subset fun j ↦ closedDisc_subset_spa Aplus T (b j)

/-- Every open disc lies in the closed disc of any radius `b'` dominating all the radii `bⱼ` at
every point of `Spa (A, A⁺)`. -/
theorem openDisc_subset_closedDisc (Aplus : Subring A) (T : A) (b : ℕ → A) {b' : A}
    (hb : ∀ j, ∀ v ∈ spa Aplus, v.toValuativeRel.vle (b j) b') :
    openDisc Aplus T b ⊆ closedDisc Aplus T b' :=
  Set.iUnion_subset fun j ↦ closedDisc_subset_closedDisc Aplus T (hb j)

/-- **A constant radius family gives the closed disc.** -/
@[simp]
theorem openDisc_const (Aplus : Subring A) (T b : A) :
    openDisc Aplus T (fun _ ↦ b) = closedDisc Aplus T b :=
  Set.iUnion_const _

/-- **Comparing open discs.** If every radius `bⱼ` is dominated by some `b'ₖ` at every point of
`Spa (A, A⁺)`, then `𝔻°(A⁺, T, b) ⊆ 𝔻°(A⁺, T, b')`. -/
theorem openDisc_subset_openDisc (Aplus : Subring A) (T : A) {b b' : ℕ → A}
    (h : ∀ j, ∃ k, ∀ v ∈ spa Aplus, v.toValuativeRel.vle (b j) (b' k)) :
    openDisc Aplus T b ⊆ openDisc Aplus T b' :=
  Set.iUnion_subset fun j ↦ by
    obtain ⟨k, hk⟩ := h j
    exact (closedDisc_subset_closedDisc Aplus T hk).trans (closedDisc_subset_openDisc Aplus T b' k)

/-- **Mutually cofinal radius families define the same open disc.** -/
theorem openDisc_eq_openDisc (Aplus : Subring A) (T : A) {b b' : ℕ → A}
    (h : ∀ j, ∃ k, ∀ v ∈ spa Aplus, v.toValuativeRel.vle (b j) (b' k))
    (h' : ∀ k, ∃ j, ∀ v ∈ spa Aplus, v.toValuativeRel.vle (b' k) (b j)) :
    openDisc Aplus T b = openDisc Aplus T b' :=
  (openDisc_subset_openDisc Aplus T h).antisymm (openDisc_subset_openDisc Aplus T h')

/-- **For unit radii the open disc is a union of rational subsets**:
`𝔻°(A⁺, T, b) = ⋃ⱼ R({T} / bⱼ)`. -/
theorem openDisc_eq_iUnion_rationalSubset (Aplus : Subring A) (T : A) {b : ℕ → A}
    (hb : ∀ j, IsUnit (b j)) :
    openDisc Aplus T b = ⋃ j, rationalSubset Aplus {T} (b j) := by
  simp only [openDisc_def, closedDisc_eq_rationalSubset Aplus T (hb _)]

/-- **An open disc with unit radii is relatively open** in `Spa (A, A⁺)`. -/
theorem isOpen_val_preimage_openDisc (Aplus : Subring A) (T : A) {b : ℕ → A}
    (hb : ∀ j, IsUnit (b j)) :
    IsOpen (Subtype.val ⁻¹' openDisc Aplus T b : Set (spa Aplus)) := by
  rw [openDisc_def, Set.preimage_iUnion]
  exact isOpen_iUnion fun j ↦ isOpen_val_preimage_closedDisc Aplus T (hb j)

/-- **Pulling back an open disc.** For a continuous ring map `φ : A → B` carrying `A⁺` into
`B⁺`, the points of `Spa (B, B⁺)` whose pullback lies in `𝔻°(A⁺, T, b)` form
`𝔻°(B⁺, φ T, φ ∘ b)`. -/
theorem comap_preimage_openDisc_inter_spa {B : Type*} [CommRing B] [TopologicalSpace B]
    {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (T : A) (b : ℕ → A) :
    comap φ ⁻¹' openDisc Aplus T b ∩ spa Bplus = openDisc Bplus (φ T) (φ ∘ b) := by
  simp only [openDisc_def, Set.preimage_iUnion, Set.iUnion_inter, Function.comp_apply,
    comap_preimage_closedDisc_inter_spa hφ hplus]

/-- The open disc with coordinate `0` is the whole adic spectrum, for every radius family,
including zero and nonunit radii: the coordinate `0` lies in every stage. -/
@[simp]
theorem openDisc_zero_left (Aplus : Subring A) (b : ℕ → A) : openDisc Aplus 0 b = spa Aplus := by
  simp [openDisc_def, Set.iUnion_const]

end TauCeti.ValuationSpectrum
