/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
public import TauCeti.Topology.ConnectedComponents
public import TauCeti.AlgebraicTopology.Sphere.Zero

/-!
# Brown's generalized Schoenflies theorem in dimension one

Let `σ` be an injective map from the unit sphere `S⁰` of a real normed space `E` of dimension `1`
into the unit sphere `S¹` of a real inner product space `F` of dimension `2`. Its image `Σ` is a
pair of points of the circle, and by the Jordan–Brouwer separation theorem
(`TauCeti.natCard_connectedComponents_sphere_compl_range_eq_two`) the complement `S¹ ∖ Σ` has
exactly two connected components. This file proves the other clauses of M. Brown's generalized
Schoenflies theorem in this dimension.

* The closure of each component `U` of `S¹ ∖ Σ` is `U ∪ Σ`, and its frontier is `Σ`
  (`TauCeti.closure_connectedComponentIn_compl_range_of_finrank_eq_one`,
  `TauCeti.frontier_connectedComponentIn_compl_range_of_finrank_eq_one`).
* The closure of each component is a closed `1`-cell: it is homeomorphic to the closed unit ball
  `D¹` of `E`, by a homeomorphism which inverts `σ` on `Σ` and carries exactly `Σ` onto the
  boundary sphere `S⁰` of `D¹`
  (`TauCeti.exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq_one`).
* For a bicollar `b` of `σ`, the two collar arcs at each point `σ x`, the points `b (x, t)` with
  `t > 0` and those with `t < 0`, lie in different components
  (`TauCeti.IsBicollar.connectedComponentIn_compl_range_ne_of_finrank_eq_one`).

In dimension one the first two statements hold for every injective `σ`, with no bicollar. The last
statement is the form that the collar clause takes here. In higher dimensions each side of a
bicollar is connected and lies in one component. Here each side consists of two arcs, one at each
point of `Σ`, and these two arcs may lie in the same component: on the unit circle, with `Σ` the
points at angles `0` and `π`, a bicollar whose angle increases with `t` at the first point and
decreases with `t` at the second has both positive arcs in the upper half of the circle.

## Proof

Fix an orientation of `F` and a unit vector `u` of `E`, so that `S⁰ = {u, -u}`. Rotating
`p = σ u` by the angle `t` (`Orientation.rotation`) parametrizes the circle, injectively on
`[0, 2π)`. If `q = σ (-u)` lies at the angle `t₀ ∈ (0, 2π)`, the components of `S¹ ∖ {p, q}` are
the open arcs of angles in `(0, t₀)` and in `(t₀, 2π)`: they are preconnected, disjoint and cover
`S¹ ∖ {p, q}`, and each is the complement of the closure of the other, hence open. Their closures
are the closed arcs, on which the parametrization is a homeomorphism from a compact interval, and
an affine map identifies that interval with `D¹`.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 5.
-/

public section

noncomputable section

namespace TauCeti

open Metric Module Set Topology Real

/-! ### The angle parametrization of a circle -/

section Param

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fact (finrank ℝ F = 2)]

/-- The point of the unit circle at angle `t` from `p`, for the orientation `o`. -/
private def circleParam (o : Orientation ℝ F (Fin 2)) (p : sphere (0 : F) 1) (t : ℝ) :
    sphere (0 : F) 1 :=
  ⟨o.rotation t p, by simp⟩

private theorem coe_circleParam (o : Orientation ℝ F (Fin 2)) (p : sphere (0 : F) 1) (t : ℝ) :
    (circleParam o p t : F) = Real.cos t • (p : F) + Real.sin t • o.rightAngleRotation p := by
  simp [circleParam, o.rotation_apply]

private theorem continuous_circleParam (o : Orientation ℝ F (Fin 2)) (p : sphere (0 : F) 1) :
    Continuous (circleParam o p) := by
  refine Continuous.subtype_mk ?_ _
  simp_rw [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
  fun_prop

private theorem circleParam_zero (o : Orientation ℝ F (Fin 2)) (p : sphere (0 : F) 1) :
    circleParam o p 0 = p := by
  ext1
  simp [coe_circleParam]

private theorem circleParam_two_pi (o : Orientation ℝ F (Fin 2)) (p : sphere (0 : F) 1) :
    circleParam o p (2 * π) = p := by
  ext1
  simp [coe_circleParam]

/-- Two angles give the same point of the circle exactly when they agree modulo `2π`. -/
private theorem circleParam_eq_circleParam_iff (o : Orientation ℝ F (Fin 2))
    (p : sphere (0 : F) 1) (s t : ℝ) :
    circleParam o p s = circleParam o p t ↔ (s : Real.Angle) = t := by
  have hp : (p : F) ≠ 0 := ne_zero_of_mem_unit_sphere p
  refine ⟨fun h ↦ ?_, fun h ↦ by simp only [circleParam, h]⟩
  have h' : o.rotation s (p : F) = o.rotation t p := congrArg Subtype.val h
  rw [← o.oangle_rotation_self_right hp s, ← o.oangle_rotation_self_right hp t, h']

/-- The parametrization is injective on every half-open interval of length `2π`. -/
private theorem injOn_circleParam (o : Orientation ℝ F (Fin 2)) (p : sphere (0 : F) 1) (a : ℝ) :
    InjOn (circleParam o p) (Ico a (a + 2 * π)) := by
  intro s hs t ht h
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1
    ((circleParam_eq_circleParam_iff o p s t).1 h)
  have h1 : (k : ℝ) < 1 := by nlinarith [hs.1, hs.2, ht.1, ht.2, pi_pos]
  have h2 : -1 < (k : ℝ) := by nlinarith [hs.1, hs.2, ht.1, ht.2, pi_pos]
  have hk0 : k = 0 := by
    have : k < 1 := by exact_mod_cast h1
    have : -1 < k := by exact_mod_cast h2
    omega
  rw [hk0, Int.cast_zero, mul_zero, sub_eq_zero] at hk
  exact hk

/-- Every point of the circle is at some angle in `[0, 2π)` from `p`. -/
private theorem exists_mem_Ico_circleParam_eq (o : Orientation ℝ F (Fin 2))
    (p y : sphere (0 : F) 1) : ∃ t ∈ Ico 0 (2 * π), circleParam o p t = y := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : Real.Angle) = o.oangle p y :=
    Real.Angle.induction_on (o.oangle p y) fun r ↦ ⟨r, rfl⟩
  refine ⟨toIcoMod two_pi_pos 0 r, by simpa using toIcoMod_mem_Ico two_pi_pos 0 r, ?_⟩
  ext1
  have hθ : ((toIcoMod two_pi_pos 0 r : ℝ) : Real.Angle) = r :=
    Real.Angle.angle_eq_iff_two_pi_dvd_sub.2 ⟨-toIcoDiv two_pi_pos 0 r, by
      rw [toIcoMod_sub_self_eq_mul]; push_cast; ring⟩
  simp only [circleParam, hθ, hr]
  exact (o.rotation_oangle_eq_iff_norm_eq _ _).2 (by simp)

end Param

/-! ### Arcs of a closed curve -/

section Arc

variable {X : Type*} {γ : ℝ → X} {a b c : ℝ}

/-- If `γ` is injective on `[0, c)` and `γ c = γ 0`, then the complement of two points `γ 0` and
`γ b` of `γ '' [0, c]` in that image consists of the two open arcs `γ '' (0, b)` and
`γ '' (b, c)`. -/
private theorem image_Icc_diff_pair (hinj : InjOn γ (Ico 0 c)) (hc : γ c = γ 0)
    (hb : b ∈ Ioo 0 c) :
    γ '' Icc 0 c \ {γ 0, γ b} = γ '' Ioo 0 b ∪ γ '' Ioo b c := by
  have h0 : (0 : ℝ) ∈ Ico 0 c := ⟨le_rfl, hb.1.trans hb.2⟩
  have hb' : b ∈ Ico 0 c := ⟨hb.1.le, hb.2⟩
  ext y
  simp only [mem_sdiff, mem_image, mem_insert_iff, mem_singleton_iff, mem_union, mem_Icc,
    mem_Ioo]
  constructor
  · rintro ⟨⟨t, ⟨ht0, htc⟩, rfl⟩, hne⟩
    rcases htc.lt_or_eq with htc | rfl
    · have ht : t ∈ Ico 0 c := ⟨ht0, htc⟩
      rcases ht0.lt_or_eq with ht0 | rfl
      · rcases lt_trichotomy t b with htb | rfl | hbt
        · exact Or.inl ⟨t, ⟨ht0, htb⟩, rfl⟩
        · exact absurd (Or.inr rfl) hne
        · exact Or.inr ⟨t, ⟨hbt, htc⟩, rfl⟩
      · exact absurd (Or.inl rfl) hne
    · exact absurd (Or.inl hc) hne
  · rintro (⟨t, ⟨ht0, htb⟩, rfl⟩ | ⟨t, ⟨hbt, htc⟩, rfl⟩)
    · have ht : t ∈ Ico 0 c := ⟨ht0.le, htb.trans hb.2⟩
      refine ⟨⟨t, ⟨ht0.le, ht.2.le⟩, rfl⟩, ?_⟩
      rintro (h | h)
      · exact ht0.ne' (hinj ht h0 h)
      · exact htb.ne (hinj ht hb' h)
    · have ht : t ∈ Ico 0 c := ⟨hb.1.le.trans hbt.le, htc⟩
      refine ⟨⟨t, ⟨ht.1, htc.le⟩, rfl⟩, ?_⟩
      rintro (h | h)
      · exact (hb.1.trans hbt).ne' (hinj ht h0 h)
      · exact hbt.ne' (hinj ht hb' h)

/-- Under the hypotheses of `image_Icc_diff_pair`, the two open arcs are disjoint. -/
private theorem disjoint_image_Ioo (hinj : InjOn γ (Ico 0 c)) (hb : b ∈ Ioo 0 c) :
    Disjoint (γ '' Ioo 0 b) (γ '' Ioo b c) := by
  rw [disjoint_left]
  rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, hst⟩
  have := hinj ⟨hb.1.le.trans ht.1.le, ht.2⟩ ⟨hs.1.le, hs.2.trans hb.2⟩ hst
  exact (hs.2.trans ht.1).ne' this

/-- The closure of an open arc is the closed arc. -/
private theorem closure_image_Ioo [TopologicalSpace X] [T2Space X] (hγ : Continuous γ)
    (hab : a < b) : closure (γ '' Ioo a b) = γ '' Icc a b := by
  refine (closure_minimal (image_mono Ioo_subset_Icc_self)
    (isCompact_Icc.image hγ).isClosed).antisymm ?_
  rw [← closure_Ioo hab.ne]
  exact image_closure_subset_closure_image hγ

/-- The closed arc is the open arc together with its two endpoints. -/
private theorem image_Icc_eq (hab : a < b) :
    γ '' Icc a b = γ '' Ioo a b ∪ {γ a, γ b} := by
  rw [← Ico_insert_right hab.le, ← Ioo_insert_left hab, image_insert_eq, image_insert_eq]
  ext y
  simp only [mem_insert_iff, mem_union]
  tauto

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine coordinate `[a, b] → [-1, 1]` sending `a` to `1` and `b` to `-1`. -/
private def arcCoord (a b s : ℝ) : ℝ := 1 - 2 * (s - a) / (b - a)

private theorem abs_arcCoord_le (hab : a < b) {s : ℝ} (hs : s ∈ Icc a b) :
    |arcCoord a b s| ≤ 1 := by
  have hba : 0 < b - a := sub_pos.2 hab
  have h0 : 0 ≤ (s - a) / (b - a) := div_nonneg (sub_nonneg.2 hs.1) hba.le
  have h1 : (s - a) / (b - a) ≤ 1 := (div_le_one hba).2 (by linarith [hs.2])
  rw [arcCoord, mul_div_assoc, abs_le]
  constructor <;> linarith

private theorem arcCoord_injective (hab : a < b) : Function.Injective (arcCoord a b) := by
  intro s t h
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  simp only [arcCoord, sub_right_inj, mul_div_assoc] at h
  field_simp at h
  linarith

private theorem arcCoord_left (a b : ℝ) : arcCoord a b a = 1 := by simp [arcCoord]

private theorem arcCoord_right (hab : a < b) : arcCoord a b b = -1 := by
  rw [arcCoord, mul_div_assoc, div_self (sub_pos.2 hab).ne']
  ring

/-- **A closed arc is a closed `1`-cell.** If `γ` is continuous and injective on `[a, b]`, and `u`
is a unit vector of a real normed space `E` of dimension `1`, then the closed arc `γ '' [a, b]` is
homeomorphic to the closed unit ball of `E`, by a homeomorphism sending the endpoints `γ a` and
`γ b` to `u` and `-u`, the two points of the unit sphere of `E`. -/
private theorem exists_homeomorph_image_Icc [TopologicalSpace X] [T2Space X] (hγ : Continuous γ)
    (hab : a < b) (hinj : InjOn γ (Icc a b)) (hE : finrank ℝ E = 1) {u : E} (hu : ‖u‖ = 1) :
    ∃ h : γ '' Icc a b ≃ₜ closedBall (0 : E) 1,
      ∀ z : γ '' Icc a b, ∀ s ∈ Icc a b, (z : X) = γ s → (h z : E) = arcCoord a b s • u := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  -- The arc is homeomorphic to `[a, b]`.
  let ψ : Icc a b ≃ₜ γ '' Icc a b :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.Set.imageOfInjOn γ (Icc a b) hinj)
      (continuous_induced_rng.2 (hγ.comp continuous_subtype_val))
  -- The interval `[a, b]` is homeomorphic to the unit ball of `E`.
  let φ : Icc a b → closedBall (0 : E) 1 := fun s ↦ ⟨arcCoord a b s • u, by
    rw [mem_closedBall_zero_iff, norm_smul, hu, mul_one, Real.norm_eq_abs]
    exact abs_arcCoord_le hab s.2⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun s t hst ↦ Subtype.ext <| arcCoord_injective hab <|
      smul_left_injective ℝ hu0 (congrArg Subtype.val hst), fun w ↦ ?_⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' u hu0).1 hE w
    have hc1 : |c| ≤ 1 := by
      have := mem_closedBall_zero_iff.1 w.2
      rwa [← hc, norm_smul, hu, mul_one, Real.norm_eq_abs] at this
    rw [abs_le] at hc1
    have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
    refine ⟨⟨a + (1 - c) * (b - a) / 2, ?_, ?_⟩, Subtype.ext ?_⟩
    · nlinarith [sub_pos.2 hab]
    · nlinarith [sub_pos.2 hab]
    · simp only [φ, arcCoord, ← hc]
      congr 1
      field_simp
      ring
  let φh : Icc a b ≃ₜ closedBall (0 : E) 1 :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ hφ)
      (Continuous.subtype_mk (by unfold arcCoord; fun_prop) _)
  -- By construction, `ψ` is `γ` and `φh` is `φ`.
  have hψ (s : Icc a b) : (ψ s : X) = γ s := rfl
  have hφh (s : Icc a b) : φh s = φ s := rfl
  refine ⟨ψ.symm.trans φh, fun z s hs hz ↦ ?_⟩
  have : ψ.symm z = ⟨s, hs⟩ := ψ.symm_apply_eq.2 (Subtype.ext (hz.trans (hψ ⟨s, hs⟩).symm))
  rw [Homeomorph.trans_apply, this, hφh]

/-- **The closure of an open arc is a closed `1`-cell.** Let `γ` be continuous and injective on
`[a, b]`, and let `σ` send each point `x` of the unit sphere `{u, -u}` of a real normed space `E` of
dimension `1` to an endpoint of the arc `γ '' (a, b)`, the point `u` to `γ a` and `-u` to `γ b`.
Then the closure of the arc is homeomorphic to the closed unit ball of `E`, by a homeomorphism
inverting `σ`. -/
private theorem exists_homeomorph_closure_image_Ioo [TopologicalSpace X] [T2Space X]
    (hγ : Continuous γ) (hab : a < b) (hinj : InjOn γ (Icc a b)) (hE : finrank ℝ E = 1) {u : E}
    (hu : ‖u‖ = 1) {σ : sphere (0 : E) 1 → X}
    (hσ : ∀ x : sphere (0 : E) 1, ((x : E) = u ∧ σ x = γ a) ∨ ((x : E) = -u ∧ σ x = γ b)) :
    ∃ h : closure (γ '' Ioo a b) ≃ₜ closedBall (0 : E) 1,
      ∀ (z : closure (γ '' Ioo a b)) x, (z : X) = σ x → (h z : E) = x := by
  obtain ⟨h, hh⟩ := exists_homeomorph_image_Icc hγ hab hinj hE hu
  refine ⟨(Homeomorph.setCongr (closure_image_Ioo hγ hab)).trans h, fun z x hz ↦ ?_⟩
  rcases hσ x with ⟨hx, hσx⟩ | ⟨hx, hσx⟩
  · rw [hσx] at hz
    simpa [arcCoord_left, hx] using hh _ a (left_mem_Icc.2 hab.le) hz
  · rw [hσx] at hz
    simpa [arcCoord_right hab, hx] using hh _ b (right_mem_Icc.2 hab.le) hz

end Arc

/-! ### The two complementary arcs of a zero-sphere in a circle -/

section DimensionOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {σ : sphere (0 : E) 1 → sphere (0 : F) 1}

/-- An open set `A` of the circle which is one of the two complementary arcs of the image of
`σ`: it is preconnected, its closure adds the image of `σ`, and the closure is a closed `1`-cell
by a homeomorphism inverting `σ` on its boundary. -/
private def IsComplementaryArc (σ : sphere (0 : E) 1 → sphere (0 : F) 1)
    (A : Set (sphere (0 : F) 1)) : Prop :=
  IsOpen A ∧ IsPreconnected A ∧ closure A = A ∪ range σ ∧
    ∃ h : closure A ≃ₜ closedBall (0 : E) 1,
      ∀ (z : closure A) x, (z : sphere (0 : F) 1) = σ x → (h z : E) = x

/-- The complement of the image of an injective map from the unit sphere of a space of dimension
`1` into the unit sphere of a space of dimension `2` is the union of two disjoint complementary
arcs. -/
private theorem exists_isComplementaryArc (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hE : finrank ℝ E = 1) (hσ : Function.Injective σ) :
    ∃ A₁ A₂ : Set (sphere (0 : F) 1), (range σ)ᶜ = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧
      IsComplementaryArc σ A₁ ∧ IsComplementaryArc σ A₂ := by
  have hF : finrank ℝ F = 2 := by rw [hEF, hE]
  have : Fact (finrank ℝ F = 2) := ⟨hF⟩
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one
  have hu1 : ‖u‖ = 1 := norm_eq_of_mem_sphere ⟨u, hu⟩
  -- The unit sphere of `E` is `{u, -u}`.
  have hpm (x : sphere (0 : E) 1) : (x : E) = u ∨ (x : E) = -u :=
    eq_or_eq_neg_of_norm_eq_of_finrank_eq_one hE ((norm_eq_of_mem_sphere x).trans hu1.symm)
  let o : Orientation ℝ F (Fin 2) := (Module.finBasisOfFinrankEq ℝ F hF).orientation
  set γ := circleParam o (σ ⟨u, hu⟩)
  set p := σ ⟨u, hu⟩
  set q := σ (-⟨u, hu⟩)
  have hγ : Continuous γ := continuous_circleParam o p
  have hγ0 : γ 0 = p := circleParam_zero o p
  have hγ2 : γ (2 * π) = p := circleParam_two_pi o p
  have hinj : InjOn γ (Ico 0 (2 * π)) := by simpa using injOn_circleParam o p 0
  have hpq : p ≠ q := fun h ↦ by
    have := congrArg Subtype.val (hσ h)
    simp only [coe_neg_sphere] at this
    have h2 := congrArg (u + ·) this
    simp only [add_neg_cancel, ← two_smul ℝ u, smul_eq_zero, two_ne_zero, false_or] at h2
    exact ne_zero_of_mem_unit_sphere ⟨u, hu⟩ h2
  -- `q` lies at an angle `t₀ ∈ (0, 2π)` from `p`.
  obtain ⟨t₀, ht₀, hγt₀⟩ : ∃ t ∈ Ico 0 (2 * π), γ t = q := exists_mem_Ico_circleParam_eq o p q
  have ht₀' : t₀ ∈ Ioo 0 (2 * π) :=
    ⟨ht₀.1.lt_of_ne fun h ↦ hpq (by rw [← hγ0, h, hγt₀]), ht₀.2⟩
  have hrange : range σ = {p, q} := by
    ext y
    refine ⟨?_, by rintro (rfl | rfl) <;> exact mem_range_self _⟩
    rintro ⟨x, rfl⟩
    rcases hpm x with hx | hx
    · exact Or.inl (congrArg σ (Subtype.ext hx))
    · exact Or.inr (congrArg σ (Subtype.ext (by simpa using hx)))
  have hsurj : γ '' Icc 0 (2 * π) = univ := eq_univ_of_forall fun y ↦ by
    obtain ⟨t, ht, rfl⟩ : ∃ t ∈ Ico 0 (2 * π), γ t = y := exists_mem_Ico_circleParam_eq o p y
    exact mem_image_of_mem γ (Ico_subset_Icc_self ht)
  have hcompl : (range σ)ᶜ = γ '' Ioo 0 t₀ ∪ γ '' Ioo t₀ (2 * π) := by
    rw [← image_Icc_diff_pair hinj (hγ2.trans hγ0.symm) ht₀', hsurj, hγ0, hγt₀, hrange,
      compl_eq_univ_sdiff]
  have hdisj := disjoint_image_Ioo hinj ht₀'
  have hcl₁' : closure (γ '' Ioo 0 t₀) = γ '' Ioo 0 t₀ ∪ range σ := by
    rw [closure_image_Ioo hγ ht₀'.1, image_Icc_eq ht₀'.1, hγ0, hγt₀, hrange]
  have hcl₂' : closure (γ '' Ioo t₀ (2 * π)) = γ '' Ioo t₀ (2 * π) ∪ range σ := by
    rw [closure_image_Ioo hγ ht₀'.2, image_Icc_eq ht₀'.2, hγ2, hγt₀, hrange, pair_comm]
  -- Each arc is the complement of the closure of the other, hence open.
  have hcompl_eq {A B : Set (sphere (0 : F) 1)} (h : (range σ)ᶜ = A ∪ B) (hAB : Disjoint A B) :
      A = (B ∪ range σ)ᶜ := by
    ext y
    have h1 := Set.ext_iff.1 h y
    have h2 : y ∈ A → y ∉ B := fun hy ↦ disjoint_left.1 hAB hy
    simp only [mem_compl_iff, mem_union] at h1 ⊢
    tauto
  -- `σ` sends `u` to `γ 0 = γ (2π)` and `-u` to `γ t₀`.
  have hσ' (x : sphere (0 : E) 1) :
      ((x : E) = u ∧ σ x = γ 0) ∨ ((x : E) = -u ∧ σ x = γ t₀) := by
    rcases hpm x with hx | hx
    · exact Or.inl ⟨hx, by rw [show x = ⟨u, hu⟩ from Subtype.ext hx, hγ0]⟩
    · exact Or.inr ⟨hx, by rw [show x = -⟨u, hu⟩ from Subtype.ext (by simpa using hx), hγt₀]⟩
  refine ⟨_, _, hcompl, hdisj, ⟨?_, isPreconnected_Ioo.image _ hγ.continuousOn, hcl₁', ?_⟩,
    ⟨?_, isPreconnected_Ioo.image _ hγ.continuousOn, hcl₂', ?_⟩⟩
  · rw [hcompl_eq hcompl hdisj, ← hcl₂']
    exact isClosed_closure.isOpen_compl
  · exact exists_homeomorph_closure_image_Ioo hγ ht₀'.1
      (hinj.mono (Icc_subset_Ico_right ht₀'.2)) hE hu1 hσ'
  · rw [union_comm] at hcompl
    rw [hcompl_eq hcompl hdisj.symm, ← hcl₁']
    exact isClosed_closure.isOpen_compl
  · refine exists_homeomorph_closure_image_Ioo hγ ht₀'.2
      ((injOn_circleParam o p t₀).mono (Icc_subset_Ico_right (by linarith [ht₀'.1]))) hE
      (u := -u) (by rw [norm_neg, hu1]) fun (x : sphere (0 : E) 1) ↦ ?_
    rw [neg_neg, hγ2, ← hγ0]
    exact (hσ' x).symm

/-- The connected component of a point `y` off the image of `σ` is one of the two complementary
arcs, and the other arc is the rest of the complement. -/
private theorem exists_connectedComponentIn_eq (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hE : finrank ℝ E = 1) (hσ : Function.Injective σ) {y : sphere (0 : F) 1}
    (hy : y ∉ range σ) :
    ∃ A A' : Set (sphere (0 : F) 1), connectedComponentIn (range σ)ᶜ y = A ∧
      (range σ)ᶜ = A ∪ A' ∧ Disjoint A A' ∧ IsComplementaryArc σ A ∧
      IsComplementaryArc σ A' := by
  obtain ⟨A₁, A₂, hcompl, hdisj, h₁, h₂⟩ := exists_isComplementaryArc hEF hE hσ
  have hy' : y ∈ A₁ ∪ A₂ := hcompl ▸ hy
  rcases hy' with hy' | hy'
  · exact ⟨A₁, A₂, by rw [hcompl, h₁.2.1.connectedComponentIn_union_eq_left h₁.1 h₂.1 hdisj hy'],
      hcompl, hdisj, h₁, h₂⟩
  · rw [union_comm] at hcompl
    exact ⟨A₂, A₁, by
      rw [hcompl, h₂.2.1.connectedComponentIn_union_eq_left h₂.1 h₁.1 hdisj.symm hy'], hcompl,
      hdisj.symm, h₂, h₁⟩

/-- **The closure of a complementary domain of two points of a circle.** Let `σ` be an injective
map from the unit sphere of a real normed space of dimension `1`, a pair of points, into the unit
sphere of a real inner product space of dimension `2`. The closure of each connected component of
the complement of its image `Σ` adds exactly `Σ`. -/
theorem closure_connectedComponentIn_compl_range_of_finrank_eq_one
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : finrank ℝ E = 1) (hσ : Function.Injective σ)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    closure (connectedComponentIn (range σ)ᶜ y) = connectedComponentIn (range σ)ᶜ y ∪ range σ := by
  obtain ⟨A, -, hA, -, -, hA', -⟩ := exists_connectedComponentIn_eq hEF hE hσ hy
  rw [hA]
  exact hA'.2.2.1

/-- **The frontier of a complementary domain of two points of a circle.** Let `σ` be an injective
map from the unit sphere of a real normed space of dimension `1` into the unit sphere of a real
inner product space of dimension `2`. Each connected component of the complement of its image `Σ`
has frontier `Σ`. -/
theorem frontier_connectedComponentIn_compl_range_of_finrank_eq_one
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : finrank ℝ E = 1) (hσ : Function.Injective σ)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    frontier (connectedComponentIn (range σ)ᶜ y) = range σ := by
  obtain ⟨A, A', hA, hcompl, -, hA', -⟩ := exists_connectedComponentIn_eq hEF hE hσ hy
  have hsub : A ⊆ (range σ)ᶜ := hcompl ▸ subset_union_left
  rw [hA, hA'.1.frontier_eq, hA'.2.2.1, union_sdiff_left]
  exact (subset_compl_iff_disjoint_left.1 hsub).sdiff_eq_left

/-- **Brown's generalized Schoenflies theorem in dimension `1`.** Let `σ` be an injective map from
the unit sphere `S⁰` of a real normed space `E` of dimension `1` into the unit sphere `S¹` of a
real inner product space of dimension `2`, with image `Σ`. The closure of each connected component
of `S¹ ∖ Σ` is homeomorphic to the closed unit ball `D¹` of `E`, by a homeomorphism `h` which
inverts `σ` on `Σ` and carries exactly `Σ` onto the boundary sphere `S⁰` of `D¹`. -/
theorem exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq_one
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : finrank ℝ E = 1) (hσ : Function.Injective σ)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : closure (connectedComponentIn (range σ)ᶜ y)) x,
        (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
      ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ := by
  obtain ⟨A, -, hA, -, -, ⟨-, -, hcl, h, hh⟩, -⟩ := exists_connectedComponentIn_eq hEF hE hσ hy
  rw [hA]
  refine ⟨h, hh, fun z ↦ ⟨fun hz ↦ ?_, ?_⟩⟩
  · -- A point sent to the boundary sphere is the image under `σ` of its image.
    let x : sphere (0 : E) 1 := ⟨h z, hz⟩
    have hx : σ x ∈ closure A := hcl ▸ Or.inr (mem_range_self x)
    have : (⟨σ x, hx⟩ : closure A) = z := h.injective (Subtype.ext (hh _ x rfl))
    exact ⟨x, congrArg Subtype.val this⟩
  · rintro ⟨x, hx⟩
    rw [hh z x hx.symm]
    exact x.2

/-- **The collar arcs at a point of a pair in a circle.** Let `b` be a bicollar of a map `σ` from
the unit sphere `S⁰` of a real normed space of dimension `1` into the unit sphere `S¹` of a real
inner product space of dimension `2`. At each point `σ x`, a point `b (x, s)` with `s > 0` and a
point `b (x, t)` with `t < 0` lie in different components of the complement of the image of `σ`.

Each collar arc at `σ x` lies in a single component
(`TauCeti.IsBicollar.image_singleton_prod_subset_connectedComponentIn`), and there are exactly
two components (`TauCeti.natCard_connectedComponents_sphere_compl_range_eq_two`), so each
component contains exactly one of the two arcs at `σ x`. -/
theorem IsBicollar.connectedComponentIn_compl_range_ne_of_finrank_eq_one
    {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1} (h : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : finrank ℝ E = 1) (x : sphere (0 : E) 1)
    {s t : ℝ} (hs : 0 < s) (ht : t < 0) :
    connectedComponentIn (range σ)ᶜ (b (x, s)) ≠ connectedComponentIn (range σ)ᶜ (b (x, t)) := by
  intro heq
  have hbs : b (x, s) ∉ range σ := fun hmem ↦ by
    have : (x, s) ∈ b ⁻¹' range σ := hmem
    rw [h.preimage_range] at this
    exact hs.ne' this.2
  obtain ⟨A, A', hA, hcompl, hdisj, -, hA'⟩ :=
    exists_connectedComponentIn_eq hEF hE h.injective hbs
  -- Both collar arcs at `σ x` lie in `A`.
  have hpos := h.image_singleton_prod_subset_connectedComponentIn x isPreconnected_Ioi
    (lt_irrefl 0) (mem_Ioi.2 hs)
  have hneg := h.image_singleton_prod_subset_connectedComponentIn x isPreconnected_Iio
    (lt_irrefl 0) (mem_Iio.2 ht)
  rw [hA] at hpos
  rw [← heq, hA] at hneg
  -- The domain is a pair of points, so the slice of `b` through `x` is an open neighbourhood of
  -- `σ x`; it meets the other arc `A'`, whose closure contains `σ x`.
  have := discreteTopology_sphere_of_finrank_eq_one hE (0 : E) 1
  have hW : IsOpen (b '' ({x} ×ˢ univ)) :=
    h.isOpenEmbedding.isOpenMap _ ((isOpen_discrete _).prod isOpen_univ)
  have hσx : σ x ∈ closure A' := hA'.2.2.1 ▸ Or.inr (mem_range_self x)
  obtain ⟨_, ⟨⟨x', r⟩, ⟨hx', -⟩, rfl⟩, hrA'⟩ :=
    mem_closure_iff.1 hσx _ hW ⟨(x, 0), ⟨rfl, trivial⟩, h.apply_zero x⟩
  rw [mem_singleton_iff] at hx'
  subst hx'
  have hA'sub : A' ⊆ (range σ)ᶜ := hcompl ▸ subset_union_right
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · exact disjoint_left.1 hdisj (hneg ⟨(x', r), ⟨rfl, hr⟩, rfl⟩) hrA'
  · rw [h.apply_zero] at hrA'
    exact hA'sub hrA' (mem_range_self x')
  · exact disjoint_left.1 hdisj (hpos ⟨(x', r), ⟨rfl, hr⟩, rfl⟩) hrA'

end DimensionOne

end TauCeti
