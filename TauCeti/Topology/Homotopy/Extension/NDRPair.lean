/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import TauCeti.Topology.ContinuousMap.ApplyProdMk
public import TauCeti.Topology.Homotopy.Extension.Basic

/-!
# NDR pairs

An *NDR pair* (neighbourhood deformation retract pair) `(X, A)` consists of a subset `A ⊆ X`
presented by explicit data: a control function `u : X → I` whose zero set is exactly `A`, and a
deformation `H : I × X → X` starting at the identity, fixing `A` pointwise, and carrying every
point with `u x < 1` into `A` at time `1`.

For an NDR pair, the bottom-and-sides subspace `J = {0} × X ∪ I × A` of the cylinder `I × X`
(`TauCeti.cylinderExtensionDomain A`) is again the zero set of an explicit control function,
`(t, x) ↦ t * u x`, and is a strong deformation retract of the cylinder by the explicit deformation
`(s, t, x) ↦ (t - s * min t (u x), H (s * min 1 (t / u x), x))`. At time `1` every point of the
cylinder lands in `J`, including the corner case `u x = t = 1`. Consequently `A` has the homotopy
extension property, and the pair `(I × X, J)` satisfies the hypotheses of the fixed-data relative
lifting theorem for Hurewicz fibrations
(`TauCeti.HasHomotopyLiftingProperty.zeroSetSDR_liftingInclusion`).

Continuity of the deformation along the zero set, where the formula divides by zero, rests on
the compactness argument `ContinuousMap.continuous_apply_prodMk_of_fixed`.

Conversely, a closed subset with the homotopy extension property carries NDR data (Strøm): if
`r` retracts the cylinder onto `J`, its second coordinate is a deformation, and
`x ↦ ⨆ t, t - (r (t, x)).1`, the largest amount by which `r` lowers a point over `x`, is a control
function (`TauCeti.NDRPair.ofRetraction`). So the closed cofibrations are exactly the subsets
admitting NDR data (`TauCeti.nonempty_ndrPair_iff`). NDR pairs `(X, A)` and `(Y, B)` have a
product `(X × Y, A × Y ∪ X × B)` (`TauCeti.NDRPair.prod`, following Steenrod and May), with
control the minimum of the two controls; this gives Strøm's product theorem for closed
cofibrations.

NDR data usually comes from a neighbourhood `U` of `A` that deformation retracts onto `A`
relative to `A`, together with a function `f : X → I` vanishing exactly on `A` and less than one
only on `U`. `TauCeti.NDRPair.ofHomotopyRel` cuts the deformation off where `3 / 4 ≤ f`, so that
it extends by the identity to all of `X`, and takes `min 1 (2 f)` as control function.

## Main declarations

* `TauCeti.NDRPair A`: NDR data for `A ⊆ X`.
* `TauCeti.NDRPair.cylinderControl`: the control function `(t, x) ↦ t * u x` of `J`.
* `TauCeti.NDRPair.cylinderDeformation`: the deformation of the cylinder onto `J`, with
  `TauCeti.NDRPair.cylinderDeformation_one_mem`.
* `TauCeti.NDRPair.cylinderRetraction`, `TauCeti.NDRPair.cylinderHomotopyRel`: the resulting
  strong deformation retraction of the cylinder onto `J`.
* `TauCeti.NDRPair.hasHomotopyExtensionProperty`: the subset of an NDR pair has the homotopy
  extension property.
* `TauCeti.NDRPair.ofRetraction`, `TauCeti.nonempty_ndrPair_iff`: **Strøm's theorem**, NDR data
  for a closed subset from a retraction of the cylinder, so that a subset admits NDR data exactly
  when it is closed and has the homotopy extension property.
* `TauCeti.NDRPair.prod`: the product of two NDR pairs.
* `TauCeti.NDRPair.ofHomotopyRel`: NDR data from a deformation of a neighbourhood `U ⊇ A` onto
  `A`, relative to `A`, and a function vanishing exactly on `A` that is less than one only on `U`.

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152, Section 6, for NDR pairs and their products.
* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 6, Section 4, for the product of
  NDR pairs.
* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142, for the control
  function of a closed cofibration and for products.
-/

public section

open Set unitInterval

universe u v

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- NDR data for a subset `A ⊆ X`: a control function `u : X → I` vanishing exactly on `A`, and
a deformation `H : I × X → X` of the identity which fixes `A` pointwise and carries every point
with `u x < 1` into `A` at time `1`. -/
structure NDRPair (A : Set X) where
  /-- The control function, vanishing exactly on `A`. -/
  control : C(X, I)
  control_eq_zero_iff (x : X) : control x = 0 ↔ x ∈ A
  /-- The deformation of `X`, starting at the identity and fixing `A`. -/
  deformation : C(I × X, X)
  deformation_zero (x : X) : deformation (0, x) = x
  deformation_of_mem (t : I) {x : X} (hx : x ∈ A) : deformation (t, x) = x
  deformation_one_mem {x : X} (hx : control x < 1) : deformation (1, x) ∈ A

attribute [simp] NDRPair.control_eq_zero_iff NDRPair.deformation_zero NDRPair.deformation_of_mem

namespace NDRPair

/-- The subset of an NDR pair is closed, being the zero set of its control function. -/
protected theorem isClosed (N : NDRPair A) : IsClosed A := by
  convert (isClosed_singleton (x := (0 : I))).preimage N.control.continuous
  ext x
  exact (N.control_eq_zero_iff x).symm

/-- The time `t * min 1 (v / u)` at which the cylinder and product deformations run a deformation
with control value `u`: in the cylinder `v` is the height, and in the product it is the control
value of the other factor. -/
private noncomputable def prodTime (t u v : I) : I :=
  t * projIcc 0 1 zero_le_one ((v : ℝ) / u)

/-- Where `v` vanishes, the deformation does not run. -/
private theorem prodTime_zero_right (t u : I) : prodTime t u 0 = 0 := by
  rw [prodTime, Icc.coe_zero, zero_div, projIcc_left]
  exact mul_zero t

/-- Where the control value `u` is positive and at most `v`, the deformation runs at full speed. -/
private theorem prodTime_of_le {t u v : I} (hu : (u : ℝ) ≠ 0) (huv : u ≤ v) :
    prodTime t u v = t := by
  rw [prodTime, projIcc_eq_one.2 ((one_le_div (lt_of_le_of_ne u.2.1 hu.symm)).2 huv), mul_one]

/-- The time of the deformation with control `u`, read off at the point `q`, is continuous where
`q` lies off the zero set of `u`. -/
private theorem continuousAt_prodTime {Z : Type*} [TopologicalSpace Z] (u : C(X, I))
    (hu : ∀ x, u x = 0 ↔ x ∈ A) {t v : Z → I} {q : Z → X} (ht : Continuous t) (hv : Continuous v)
    (hq : Continuous q) {z : Z} (hz : q z ∉ A) :
    ContinuousAt (fun z ↦ prodTime (t z) (u (q z)) (v z)) z :=
  ht.continuousAt.mul (u.continuousAt_projIcc_div_of_notMem hu hv hq hz)

variable (N : NDRPair A)

/-- The control function `(t, x) ↦ t * u x` of the bottom-and-sides subspace
`{0} × X ∪ I × A` of the cylinder. -/
def cylinderControl : C(I × X, I) :=
  ⟨fun z ↦ z.1 * N.control z.2, by fun_prop⟩

@[simp]
theorem cylinderControl_apply (z : I × X) : N.cylinderControl z = z.1 * N.control z.2 := (rfl)

/-- The control function of the cylinder vanishes exactly on `{0} × X ∪ I × A`. -/
theorem cylinderControl_eq_zero_iff (z : I × X) :
    N.cylinderControl z = 0 ↔ z ∈ cylinderExtensionDomain A := by
  rw [cylinderControl_apply, mem_cylinderExtensionDomain_iff, ← N.control_eq_zero_iff]
  exact mul_eq_zero

private theorem cylinderHeight_mem (w : I × I × X) :
    (w.2.1 : ℝ) - w.1 * min (w.2.1 : ℝ) (N.control w.2.2) ∈ I := by
  have h₁ : (w.1 : ℝ) * min (w.2.1 : ℝ) (N.control w.2.2) ≤ min (w.2.1 : ℝ) (N.control w.2.2) :=
    mul_le_of_le_one_left (le_min w.2.1.2.1 (N.control w.2.2).2.1) w.1.2.2
  have h₂ : 0 ≤ (w.1 : ℝ) * min (w.2.1 : ℝ) (N.control w.2.2) :=
    mul_nonneg w.1.2.1 (le_min w.2.1.2.1 (N.control w.2.2).2.1)
  constructor <;> linarith [min_le_left (w.2.1 : ℝ) (N.control w.2.2), w.2.1.2.2]

/-- The deformation of the cylinder `I × X` onto `{0} × X ∪ I × A`: at time `s` it sends
`(t, x)` to `(t - s * min t (u x), H (s * min 1 (t / u x), x))`. For `t > 0` the height is
`t * (1 - s * min 1 (u x / t))`. -/
noncomputable def cylinderDeformation : C(I × (I × X), I × X) where
  toFun w :=
    (⟨_, N.cylinderHeight_mem w⟩, N.deformation (prodTime w.1 (N.control w.2.2) w.2.1, w.2.2))
  continuous_toFun :=
    (Continuous.subtype_mk (by fun_prop) _).prodMk
      (N.deformation.continuous_apply_prodMk_of_fixed (fun t _ hx ↦ N.deformation_of_mem t hx)
        (by fun_prop) fun _ hw ↦ continuousAt_prodTime N.control N.control_eq_zero_iff
          continuous_fst (by fun_prop) (by fun_prop) hw)

@[simp]
theorem coe_cylinderDeformation_fst (s t : I) (x : X) :
    ((N.cylinderDeformation (s, t, x)).1 : ℝ) = t - s * min (t : ℝ) (N.control x) :=
  (rfl)

@[simp]
theorem cylinderDeformation_snd (s t : I) (x : X) :
    (N.cylinderDeformation (s, t, x)).2 =
      N.deformation (s * projIcc 0 1 zero_le_one ((t : ℝ) / N.control x), x) :=
  (rfl)

/-- At time `0` the cylinder deformation is the identity. -/
@[simp]
theorem cylinderDeformation_zero (z : I × X) : N.cylinderDeformation (0, z) = z := by
  obtain ⟨t, x⟩ := z
  refine Prod.ext (Subtype.ext ?_) ?_
  · simp
  · simp

/-- The cylinder deformation fixes `{0} × X ∪ I × A` pointwise. -/
@[simp]
theorem cylinderDeformation_of_mem (s : I) {z : I × X} (hz : z ∈ cylinderExtensionDomain A) :
    N.cylinderDeformation (s, z) = z := by
  obtain ⟨t, x⟩ := z
  rcases mem_cylinderExtensionDomain_iff.1 hz with ht | hx
  · obtain rfl : t = 0 := ht
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp [min_eq_left (N.control x).2.1]
    · simp
  · have hu : (N.control x : ℝ) = 0 := by rw [(N.control_eq_zero_iff x).2 hx, Icc.coe_zero]
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp [hu, min_eq_right t.2.1]
    · rw [cylinderDeformation_snd, N.deformation_of_mem _ hx]

/-- At time `1` the cylinder deformation lands in `{0} × X ∪ I × A`. Where `t ≤ u x` it reaches
the bottom of the cylinder; otherwise `u x < t ≤ 1`, so `H (1, x)` lies in `A`. This includes
the corner case `u x = t = 1`, which reaches the bottom. -/
theorem cylinderDeformation_one_mem (z : I × X) :
    N.cylinderDeformation (1, z) ∈ cylinderExtensionDomain A := by
  obtain ⟨t, x⟩ := z
  rw [mem_cylinderExtensionDomain_iff]
  rcases le_or_gt (t : ℝ) (N.control x) with htu | hut
  · left
    ext
    simp [min_eq_left htu]
  · right
    rw [cylinderDeformation_snd]
    by_cases hx : x ∈ A
    · rw [N.deformation_of_mem _ hx]
      exact hx
    · have hpos : 0 < (N.control x : ℝ) :=
        (N.control x).2.1.lt_of_ne ((coe_ne_zero_iff_notMem N.control_eq_zero_iff x).2 hx).symm
      have hproj : projIcc 0 1 zero_le_one ((t : ℝ) / N.control x) = 1 :=
        projIcc_eq_one.2 ((one_le_div hpos).2 hut.le)
      rw [hproj, one_mul]
      exact N.deformation_one_mem (Subtype.coe_lt_coe.1 (hut.trans_le t.2.2))

/-- The retraction of the cylinder `I × X` onto `{0} × X ∪ I × A`, the end of the cylinder
deformation. -/
noncomputable def cylinderRetraction : C(I × X, cylinderExtensionDomain A) :=
  ⟨fun z ↦ ⟨N.cylinderDeformation (1, z), N.cylinderDeformation_one_mem z⟩, by fun_prop⟩

@[simp]
theorem coe_cylinderRetraction_apply (z : I × X) :
    (N.cylinderRetraction z : I × X) = N.cylinderDeformation (1, z) := (rfl)

/-- The cylinder retraction fixes the points of `{0} × X ∪ I × A`. -/
@[simp]
theorem cylinderRetraction_apply_coe (z : cylinderExtensionDomain A) :
    N.cylinderRetraction z = z :=
  Subtype.ext (N.cylinderDeformation_of_mem 1 z.2)

/-- The cylinder deformation is a strong deformation retraction of `I × X` onto
`{0} × X ∪ I × A`: a homotopy relative to that subspace from the identity to the retraction. -/
noncomputable def cylinderHomotopyRel :
    (ContinuousMap.id (I × X)).HomotopyRel
      ((ContinuousMap.subtypeVal _).comp N.cylinderRetraction) (cylinderExtensionDomain A) where
  toContinuousMap := N.cylinderDeformation
  map_zero_left := N.cylinderDeformation_zero
  map_one_left _ := rfl
  prop' s z hz := by
    simp only [ContinuousMap.coe_mk, ContinuousMap.id_apply]
    exact N.cylinderDeformation_of_mem s hz

@[simp]
theorem cylinderHomotopyRel_apply (w : I × (I × X)) :
    N.cylinderHomotopyRel w = N.cylinderDeformation w := (rfl)

/-- The subset of an NDR pair has the homotopy extension property: the cylinder retracts onto
`{0} × X ∪ I × A`. -/
protected theorem hasHomotopyExtensionProperty (N : NDRPair A) :
    HasHomotopyExtensionProperty A :=
  hasHomotopyExtensionProperty_of_retraction (r := (ContinuousMap.subtypeVal _).comp
      N.cylinderRetraction) N.isClosed (fun z ↦ (N.cylinderRetraction z).2)
    fun z hz ↦ congrArg Subtype.val (N.cylinderRetraction_apply_coe ⟨z, hz⟩)

section OfRetraction

variable (r : C(I × X, I × X))

/-- The largest amount `⨆ t, t - (r (t, x)).1` by which `r` lowers a point of the cylinder over
`x`. -/
private noncomputable def retractionDrop (x : X) : ℝ :=
  ⨆ t : I, (t : ℝ) - (r (t, x)).1

private theorem bddAbove_range_drop (x : X) :
    BddAbove (range fun t : I ↦ (t : ℝ) - (r (t, x)).1) :=
  ⟨1, forall_mem_range.2 fun t ↦ by linarith [t.2.2, (r (t, x)).1.2.1]⟩

private theorem sub_le_retractionDrop (t : I) (x : X) :
    (t : ℝ) - (r (t, x)).1 ≤ retractionDrop r x :=
  le_ciSup (bddAbove_range_drop r x) t

private theorem retractionDrop_le_one (x : X) : retractionDrop r x ≤ 1 :=
  ciSup_le fun t ↦ by linarith [t.2.2, (r (t, x)).1.2.1]

private theorem continuous_retractionDrop : Continuous (retractionDrop r) := by
  have h := isCompact_univ.continuous_sSup (f := fun (x : X) (t : I) ↦ (t : ℝ) - (r (t, x)).1)
    (by fun_prop)
  unfold retractionDrop
  simpa only [image_univ, sSup_range] using h

variable {r} (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
  (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p)
include hr'

private theorem retractionDrop_nonneg (x : X) : 0 ≤ retractionDrop r x := by
  simpa [hr' _ (zero_mem_cylinderExtensionDomain x)] using sub_le_retractionDrop r 0 x

private theorem retractionDrop_eq_zero_of_mem {x : X} (hx : x ∈ A) : retractionDrop r x = 0 := by
  simp [retractionDrop, hr' _ (mem_cylinderExtensionDomain_of_mem hx)]

include hr

/-- If `r` lowers no point over `x`, then `x ∈ A`: over every positive time `r` does not reach
the bottom of the cylinder, so it lands over `A`, and `A` is closed. -/
private theorem mem_of_retractionDrop_le_zero (hA : IsClosed A) {x : X}
    (hx : retractionDrop r x ≤ 0) : x ∈ A := by
  have hpos : Ioi (0 : I) ⊆ {t | (r (t, x)).2 ∈ A} := fun t ht ↦ by
    refine (mem_cylinderExtensionDomain_iff.1 (hr (t, x))).resolve_left fun h ↦ ?_
    have := (sub_le_retractionDrop r t x).trans hx
    rw [h, Icc.coe_zero, sub_zero] at this
    exact not_le.2 ht (Subtype.coe_le_coe.1 (this.trans_eq Icc.coe_zero.symm))
  have hcl : IsClosed {t : I | (r (t, x)).2 ∈ A} := hA.preimage (by fun_prop)
  have h0 : (0 : I) ∈ closure (Ioi 0) := by
    rw [closure_Ioi' ⟨1, zero_lt_one⟩]
    exact mem_Ici.2 le_rfl
  simpa [hr' _ (zero_mem_cylinderExtensionDomain x)] using hcl.closure_subset_iff.2 hpos h0

/-- **Strøm's theorem.** A retraction `r` of the cylinder `I × X` onto `{0} × X ∪ I × A`, for a
closed subset `A`, gives NDR data for `A`: the deformation is the second coordinate of `r`, and
the control function is `x ↦ ⨆ t, t - (r (t, x)).1`, the largest amount by which `r` lowers a
point of the cylinder over `x`. -/
noncomputable def ofRetraction (hA : IsClosed A) : NDRPair A where
  control := ⟨fun x ↦ ⟨retractionDrop r x, retractionDrop_nonneg hr' x, retractionDrop_le_one r x⟩,
    (continuous_retractionDrop r).subtype_mk _⟩
  control_eq_zero_iff x := by
    rw [ContinuousMap.coe_mk, ← Subtype.coe_inj, Icc.coe_zero]
    exact ⟨fun h ↦ mem_of_retractionDrop_le_zero hr hr' hA h.le,
      retractionDrop_eq_zero_of_mem hr'⟩
  deformation := ⟨fun p ↦ (r p).2, by fun_prop⟩
  deformation_zero x := by simp [hr' _ (zero_mem_cylinderExtensionDomain x)]
  deformation_of_mem t x hx := by simp [hr' _ (mem_cylinderExtensionDomain_of_mem hx)]
  deformation_one_mem {x} hx := by
    refine (mem_cylinderExtensionDomain_iff.1 (hr (1, x))).resolve_left fun h ↦ ?_
    have := (sub_le_retractionDrop r 1 x).trans_lt (Subtype.coe_lt_coe.2 hx)
    simp [h] at this

/-- The control function of `ofRetraction` is `x ↦ ⨆ t, t - (r (t, x)).1`. -/
@[simp]
theorem coe_ofRetraction_control (hA : IsClosed A) (x : X) :
    ((ofRetraction hr hr' hA).control x : ℝ) = ⨆ t : I, (t : ℝ) - (r (t, x)).1 :=
  (rfl)

/-- The deformation of `ofRetraction` is the second coordinate of the retraction. -/
@[simp]
theorem ofRetraction_deformation (hA : IsClosed A) (p : I × X) :
    (ofRetraction hr hr' hA).deformation p = (r p).2 :=
  (rfl)

end OfRetraction

section OfHomotopyRel

variable {U : Set X} {hAU : A ⊆ U} {r : C(U, A)}
  (D : (ContinuousMap.id U).HomotopyRel ((ContinuousMap.inclusion hAU).comp r) {x | ↑x ∈ A})
  (f : C(X, I))

/-- The time `t * max 0 (min 1 (3 - 4 f x))` at which `ofHomotopyRel` reads off the deformation
`D`. -/
private noncomputable def cutoffTime (p : I × X) : I :=
  p.1 * projIcc 0 1 zero_le_one (3 - 4 * (f p.2 : ℝ))

private theorem continuous_cutoffTime : Continuous (cutoffTime f) := by
  unfold cutoffTime
  fun_prop

open scoped Classical in
/-- The deformation `D` cut off by `cutoffTime`, and extended by the identity off `U`. -/
private noncomputable def cutoff (p : I × X) : X :=
  if h : p.2 ∈ U then D (cutoffTime f p, ⟨p.2, h⟩) else p.2

private theorem cutoff_of_mem {p : I × X} (h : p.2 ∈ U) :
    cutoff D f p = D (cutoffTime f p, ⟨p.2, h⟩) := by
  simp only [cutoff, h, ↓reduceDIte]

private theorem cutoff_of_notMem {p : I × X} (h : p.2 ∉ U) : cutoff D f p = p.2 := by
  simp only [cutoff, h, ↓reduceDIte]

/-- Where `3 / 4 ≤ f`, the cut-off deformation does not move the point. -/
private theorem cutoff_of_le {x : X} (hx : 3 / 4 ≤ (f x : ℝ)) (t : I) : cutoff D f (t, x) = x := by
  by_cases h : x ∈ U
  · have h0 : cutoffTime f (t, x) = 0 := by
      have hle : 3 - 4 * (f x : ℝ) ≤ 0 := by linarith
      rw [cutoffTime, projIcc_eq_zero.2 hle]
      exact mul_zero t
    rw [cutoff_of_mem D f h, h0, D.apply_zero, ContinuousMap.id_apply]
  · exact cutoff_of_notMem D f h

variable {f} in
/-- On the open set `{f < 1} ⊆ U` the cut-off deformation is continuous, being a composite of
`D`. -/
private theorem continuousOn_cutoff (hfU : ∀ x, f x < 1 → x ∈ U) :
    ContinuousOn (cutoff D f) (univ ×ˢ {x | f x < 1}) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hU (p : (univ ×ˢ {x | f x < 1} : Set (I × X))) : p.1.2 ∈ U := hfU _ p.2.2
  refine (continuous_subtype_val.comp (D.continuous.comp (Continuous.prodMk
    ((continuous_cutoffTime f).comp continuous_subtype_val)
    (Continuous.subtype_mk (by fun_prop) hU)))).congr fun p ↦ ?_
  simp only [Function.comp_apply, domRestrict_apply, cutoff_of_mem D f (hU p)]

variable {f} in
private theorem continuous_cutoff (hfU : ∀ x, f x < 1 → x ∈ U) : Continuous (cutoff D f) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rcases lt_or_ge (f p.2 : ℝ) 1 with hp | hp
  · exact (continuousOn_cutoff D hfU).continuousAt (prod_mem_nhds Filter.univ_mem
      ((isOpen_lt f.continuous continuous_const).mem_nhds (Subtype.coe_lt_coe.1 hp)))
  · have hlt : (3 / 4 : ℝ) < f p.2 := by linarith
    refine continuousAt_snd.congr (Filter.eventuallyEq_of_mem (prod_mem_nhds Filter.univ_mem
      ((isOpen_lt continuous_const (continuous_subtype_val.comp f.continuous)).mem_nhds hlt))
        fun q hq ↦ ?_)
    exact (cutoff_of_le D f (le_of_lt hq.2) q.1).symm

private theorem coe_projIcc_two_mul (x : X) :
    (projIcc 0 1 zero_le_one (2 * (f x : ℝ)) : ℝ) = min 1 (2 * (f x : ℝ)) := by
  rw [Set.coe_projIcc]
  exact max_eq_right (le_min zero_le_one (mul_nonneg zero_le_two (f x).2.1))

variable (hAU) in
/-- **NDR data from a deformation of a neighbourhood.** Let `D` be a homotopy, relative to `A`,
from the identity of a set `U ⊇ A` to a retraction onto `A`, and let `f : X → I` vanish exactly on
`A` with `{f < 1} ⊆ U`. Cutting `D` off by the time factor `max 0 (min 1 (3 - 4 f))` gives NDR
data for `A`, with control function `min 1 (2 f)`. The deformation runs in full where `f ≤ 1 / 2`
and moves no point where `3 / 4 ≤ f`. The set `U` need not be open. -/
noncomputable def ofHomotopyRel (hf : ∀ x, f x = 0 ↔ x ∈ A) (hfU : ∀ x, f x < 1 → x ∈ U) :
    NDRPair A where
  control := ⟨fun x ↦ projIcc 0 1 zero_le_one (2 * (f x : ℝ)), by fun_prop⟩
  control_eq_zero_iff x := by
    rw [← hf, ContinuousMap.coe_mk, ← Subtype.coe_inj, ← Subtype.coe_inj, coe_projIcc_two_mul,
      Icc.coe_zero]
    have := (f x).2.1
    constructor <;> intro h
    · rcases min_eq_iff.1 h with h | h <;> linarith [h.1]
    · simp [h]
  deformation := ⟨cutoff D f, continuous_cutoff D hfU⟩
  deformation_zero x := by
    by_cases h : x ∈ U
    · rw [ContinuousMap.coe_mk, cutoff_of_mem D f h, cutoffTime, zero_mul, D.apply_zero,
        ContinuousMap.id_apply]
    · exact cutoff_of_notMem D f h
  deformation_of_mem t x hx := by
    have hxA : (⟨x, hAU hx⟩ : U) ∈ {x : U | ↑x ∈ A} := by
      rwa [mem_ofPred_eq]
    rw [ContinuousMap.coe_mk, cutoff_of_mem D f (hAU hx), D.eq_fst _ hxA, ContinuousMap.id_apply]
  deformation_one_mem {x} hx := by
    have hx : (f x : ℝ) < 1 / 2 := by
      have := Subtype.coe_lt_coe.2 hx
      rw [ContinuousMap.coe_mk, coe_projIcc_two_mul, Icc.coe_one] at this
      linarith [min_lt_iff.1 this |>.resolve_left (lt_irrefl 1)]
    have hU := hfU x (Subtype.coe_lt_coe.1 (hx.trans (by norm_num)))
    have hle : (1 : ℝ) ≤ 3 - 4 * (f x : ℝ) := by linarith
    have h1 : cutoffTime f (1, x) = 1 := by
      rw [cutoffTime, projIcc_eq_one.2 hle, one_mul]
    rw [ContinuousMap.coe_mk, cutoff_of_mem D f hU, h1, D.apply_one]
    exact (r ⟨x, hU⟩).2

variable (hf : ∀ x, f x = 0 ↔ x ∈ A) (hfU : ∀ x, f x < 1 → x ∈ U)

/-- The control function of `ofHomotopyRel` is `min 1 (2 f)`. -/
@[simp]
theorem coe_ofHomotopyRel_control (x : X) :
    ((ofHomotopyRel hAU D f hf hfU).control x : ℝ) = min 1 (2 * (f x : ℝ)) :=
  coe_projIcc_two_mul f x

/-- At a point of `U`, the deformation of `ofHomotopyRel` follows `D` with time scaled by
`max 0 (min 1 (3 - 4 f))`. -/
theorem ofHomotopyRel_deformation_of_mem (t : I) {x : X} (hx : x ∈ U) :
    (ofHomotopyRel hAU D f hf hfU).deformation (t, x) =
      D (t * projIcc 0 1 zero_le_one (3 - 4 * (f x : ℝ)), ⟨x, hx⟩) :=
  cutoff_of_mem D f (p := (t, x)) hx

/-- Off `U`, the deformation of `ofHomotopyRel` does not move the point. -/
theorem ofHomotopyRel_deformation_of_notMem (t : I) {x : X} (hx : x ∉ U) :
    (ofHomotopyRel hAU D f hf hfU).deformation (t, x) = x :=
  cutoff_of_notMem D f (p := (t, x)) hx

/-- Where `f ≤ 1 / 2`, the deformation of `ofHomotopyRel` is `D` itself. -/
theorem ofHomotopyRel_deformation_of_le_half (t : I) {x : X} (hx : (f x : ℝ) ≤ 1 / 2) :
    (ofHomotopyRel hAU D f hf hfU).deformation (t, x) =
      D (t, ⟨x, hfU x (Subtype.coe_lt_coe.1 (hx.trans_lt (by norm_num)))⟩) := by
  have hle : (1 : ℝ) ≤ 3 - 4 * (f x : ℝ) := by linarith
  rw [ofHomotopyRel_deformation_of_mem, projIcc_eq_one.2 hle]
  exact congrArg (fun s ↦ (D (s, _) : X)) (mul_one t)

/-- Where `3 / 4 ≤ f`, the deformation of `ofHomotopyRel` does not move the point. -/
theorem ofHomotopyRel_deformation_of_three_quarters_le (t : I) {x : X}
    (hx : 3 / 4 ≤ (f x : ℝ)) : (ofHomotopyRel hAU D f hf hfU).deformation (t, x) = x :=
  cutoff_of_le D f hx t

end OfHomotopyRel

section Prod

variable {Y : Type v} [TopologicalSpace Y] {B : Set Y} (M : NDRPair B)

/-- **The product of NDR pairs.** If `(X, A)` and `(Y, B)` are NDR pairs with controls `u`, `v`
and deformations `H`, `K`, then so is `(X × Y, A × Y ∪ X × B)`, with control
`(x, y) ↦ min (u x) (v y)` and deformation
`(t, x, y) ↦ (H (t * min 1 (v y / u x), x), K (t * min 1 (u x / v y), y))`: the factor with the
smaller control value runs at full speed, and the other one in proportion. -/
noncomputable def prod : NDRPair (A ×ˢ (univ : Set Y) ∪ (univ : Set X) ×ˢ B) where
  control := ⟨fun p ↦ min (N.control p.1) (M.control p.2), by fun_prop⟩
  control_eq_zero_iff p := by
    simp only [ContinuousMap.coe_mk, mem_union, mem_prod, mem_univ, and_true, true_and,
      ← N.control_eq_zero_iff, ← M.control_eq_zero_iff]
    exact min_eq_bot
  deformation :=
    ⟨fun w ↦ (N.deformation (prodTime w.1 (N.control w.2.1) (M.control w.2.2), w.2.1),
      M.deformation (prodTime w.1 (M.control w.2.2) (N.control w.2.1), w.2.2)),
    (N.deformation.continuous_apply_prodMk_of_fixed (fun t _ hx ↦ N.deformation_of_mem t hx)
      (by fun_prop) fun _ hw ↦ continuousAt_prodTime N.control N.control_eq_zero_iff
        (by fun_prop) (by fun_prop) (by fun_prop) hw).prodMk
    (M.deformation.continuous_apply_prodMk_of_fixed (fun t _ hy ↦ M.deformation_of_mem t hy)
      (by fun_prop) fun _ hw ↦ continuousAt_prodTime M.control M.control_eq_zero_iff
        (by fun_prop) (by fun_prop) (by fun_prop) hw)⟩
  deformation_zero p := by simp [prodTime]
  deformation_of_mem t p hp := by
    obtain ⟨x, y⟩ := p
    rcases hp with ⟨hx, -⟩ | ⟨-, hy⟩
    · simp [N.deformation_of_mem _ hx, (N.control_eq_zero_iff x).2 hx, prodTime_zero_right]
    · simp [M.deformation_of_mem _ hy, (M.control_eq_zero_iff y).2 hy, prodTime_zero_right]
  deformation_one_mem {p} hp := by
    obtain ⟨x, y⟩ := p
    simp only [ContinuousMap.coe_mk] at hp ⊢
    rcases le_total (N.control x) (M.control y) with h | h
    · rw [min_eq_left h] at hp
      refine Or.inl ⟨?_, mem_univ _⟩
      by_cases hx : x ∈ A
      · rw [N.deformation_of_mem _ hx]
        exact hx
      · rw [prodTime_of_le ((coe_ne_zero_iff_notMem N.control_eq_zero_iff x).2 hx) h]
        exact N.deformation_one_mem hp
    · rw [min_eq_right h] at hp
      refine Or.inr ⟨mem_univ _, ?_⟩
      by_cases hy : y ∈ B
      · rw [M.deformation_of_mem _ hy]
        exact hy
      · rw [prodTime_of_le ((coe_ne_zero_iff_notMem M.control_eq_zero_iff y).2 hy) h]
        exact M.deformation_one_mem hp

/-- The control function of the product of NDR pairs is the minimum of the two controls. -/
@[simp]
theorem prod_control_apply (p : X × Y) :
    (N.prod M).control p = min (N.control p.1) (M.control p.2) :=
  (rfl)

/-- The deformation of the product of NDR pairs runs the factor with the smaller control value at
full speed, and the other one in proportion. -/
theorem prod_deformation_apply (t : I) (x : X) (y : Y) :
    (N.prod M).deformation (t, x, y) =
      (N.deformation (t * projIcc 0 1 zero_le_one ((M.control y : ℝ) / N.control x), x),
        M.deformation (t * projIcc 0 1 zero_le_one ((N.control x : ℝ) / M.control y), y)) :=
  (rfl)

end Prod

end NDRPair

/-- **Strøm's characterization of closed cofibrations**: a subset admits NDR data exactly when it
is closed and has the homotopy extension property. -/
theorem nonempty_ndrPair_iff : Nonempty (NDRPair A) ↔ IsClosed A ∧ HasHomotopyExtensionProperty A :=
  ⟨fun ⟨N⟩ ↦ ⟨N.isClosed, N.hasHomotopyExtensionProperty⟩, fun ⟨hA, h⟩ ↦
    let ⟨_, hr, hr'⟩ := h.exists_retraction
    ⟨NDRPair.ofRetraction hr hr' hA⟩⟩

end TauCeti
