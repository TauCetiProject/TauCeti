/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import TauCeti.Topology.Homotopy.Isotopy.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Topology.Covering.Prod
import TauCeti.Topology.Homotopy.Isotopy.Alexander
import TauCeti.Topology.Homotopy.Isotopy.Comp

/-!
# Homeomorphisms of the torus fixing the two coordinate circles

A homeomorphism `h` of the torus `S¹ × S¹` which fixes every point of the two coordinate circles
`S¹ × {1}` and `{1} × S¹` is isotopic to the identity, through homeomorphisms fixing those circles
(`Homeomorph.exists_ambientIsotopy_final_eq_of_apply_mk_one_eq`). Consequently two homeomorphisms
of the torus which agree on the two coordinate circles are isotopic
(`Homeomorph.isotopic_of_apply_mk_one_eq`). This is the last step of the Alexander method for the
torus: the two circles cut the torus into a disc, and a homeomorphism of a disc fixing its boundary
is isotopic to the identity by Alexander's trick (`Homeomorph.alexanderIsotopyClosedBall`).

The torus is the image of the square `[-1, 1]²`, the closed unit ball of `ℝ × ℝ` for the sup norm,
under the covering `(x, y) ↦ (exp (iπ(x + 1)), exp (iπ(y + 1)))`, which sends the boundary of the
square onto the two coordinate circles and is injective on its interior. The proof has three steps.

* **The lift preserves the square.** Since `h` fixes the point `(1, 1)`, the composite of `h` with
  the covering lifts to a continuous map `G` of `ℝ × ℝ` fixing `(-1, -1)`. Along each of the four
  lines through the sides of the square, the covering lands in the coordinate circles, where `h` is
  the identity; so `G` restricted to such a line is a lift of the covering itself, and is the
  identity by uniqueness of lifts. Off the coordinate circles `h` takes values off the coordinate
  circles, so the coordinates of `G` avoid `±1` on the open square. Since the first coordinate of
  `G` equals `0` at the point `(0, -1)` of the bottom side, the intermediate value theorem on the
  preconnected set `(-1, 1) × [-1, 1)` keeps it in `(-1, 1)`, and similarly for the second
  coordinate. So `G` maps the square to itself, fixing its boundary. The lift of `h⁻¹` is inverse
  to it, again by uniqueness of lifts, so `G` restricts to a homeomorphism of the square.
* **Alexander's trick** joins this homeomorphism of the square to the identity through
  homeomorphisms of the square fixing its boundary.
* **Descent.** Two distinct points of the square with the same image in the torus lie on its
  boundary, which is fixed throughout. So the isotopy of the square descends to the torus, through
  the quotient map `[0, 1] × [-1, 1]² → [0, 1] × (S¹ × S¹)` from a compact space to a Hausdorff
  space. Its level-preserving total map is a continuous bijection of the compact Hausdorff space
  `[0, 1] × (S¹ × S¹)`, hence a homeomorphism.

The remaining step of the classification of homeomorphisms of the torus up to isotopy, that a
homeomorphism homotopic to a linear one can be isotoped to agree with it on the two coordinate
circles, is not proved here.

## Main results

* `Homeomorph.exists_ambientIsotopy_final_eq_of_apply_mk_one_eq`: a homeomorphism of the torus
  fixing the two coordinate circles pointwise is the end of an ambient isotopy fixing them at every
  time.
* `Homeomorph.isotopic_of_apply_mk_one_eq`: two homeomorphisms of the torus agreeing on the two
  coordinate circles are isotopic.

## References

* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Princeton University Press (2012),
  Section 2.2, Lemma 2.1 (the Alexander lemma) and Theorem 2.5 (the mapping class group of the
  torus), and Section 2.3 (the Alexander method).
-/

public section

noncomputable section

open Function Metric Set Real unitInterval

namespace TauCeti.TorusIsotopy

/-! ### The covering of the torus by the square -/

/-- The covering `ℝ × ℝ → S¹ × S¹`, `(x, y) ↦ (exp (iπ(x + 1)), exp (iπ(y + 1)))`, which maps the
square `[-1, 1]²` onto the torus and its boundary onto the two coordinate circles. -/
private def cover : C(ℝ × ℝ, Circle × Circle) :=
  ⟨fun v ↦ (Circle.exp (π * (v.1 + 1)), Circle.exp (π * (v.2 + 1))), by fun_prop⟩

private theorem cover_apply (v : ℝ × ℝ) :
    cover v = (Circle.exp (π * (v.1 + 1)), Circle.exp (π * (v.2 + 1))) :=
  (rfl)

/-- The covering sends the lines through the sides of the square to `1`. -/
private theorem exp_pi_mul_add_one_eq_one {x : ℝ} (hx : x = -1 ∨ x = 1) :
    Circle.exp (π * (x + 1)) = 1 := by
  rcases hx with rfl | rfl
  · simp
  · rw [show π * (1 + 1) = 2 * π by ring, Circle.exp_two_pi]

/-- The covering sends the open interval `(-1, 1)` away from `1`. -/
private theorem exp_pi_mul_add_one_ne_one {x : ℝ} (hx : |x| < 1) :
    Circle.exp (π * (x + 1)) ≠ 1 := by
  rw [Ne, Circle.exp_eq_one]
  rintro ⟨n, hn⟩
  obtain ⟨hx₁, hx₂⟩ := abs_lt.1 hx
  have h₀ : (0 : ℝ) < n := by nlinarith [pi_pos]
  have h₁ : (n : ℝ) < 1 := by nlinarith [pi_pos]
  have h₀' : 0 < n := by exact_mod_cast h₀
  have h₁' : n < 1 := by exact_mod_cast h₁
  omega

/-- The covering is a covering map: it is the product of two copies of the exponential
`ℝ → S¹`, precomposed with the affine homeomorphism `x ↦ π(x + 1)`. -/
private theorem isCoveringMap_cover : IsCoveringMap cover := by
  let a : ℝ ≃ₜ ℝ := (Homeomorph.addRight 1).trans (Homeomorph.mulLeft₀ π pi_ne_zero)
  have ha : IsCoveringMap (Circle.exp ∘ a) := Circle.isCoveringMap_exp.comp_homeomorph a
  exact ha.prodMap ha

/-- **Uniqueness of lifts through the covering.** Two continuous maps from a preconnected space to
`ℝ × ℝ` with the same image in the torus, and agreeing at one point, are equal. -/
private theorem eq_of_cover_eq {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {F F' : A → ℝ × ℝ} (hF : Continuous F) (hF' : Continuous F')
    (h : ∀ a, cover (F a) = cover (F' a)) {a₀ : A} (h₀ : F a₀ = F' a₀) (a : A) : F a = F' a :=
  congrFun (isCoveringMap_cover.eq_of_comp_eq hF hF' (funext h) a₀ h₀) a

/-- A homeomorphism of the torus fixing `(1, 1)`, read through the covering, lifts to a continuous
self-map of `ℝ × ℝ` fixing `(-1, -1)`. -/
private theorem exists_lift (h : Circle × Circle ≃ₜ Circle × Circle) (h₁₁ : h (1, 1) = (1, 1)) :
    ∃ G : C(ℝ × ℝ, ℝ × ℝ), G (-1, -1) = (-1, -1) ∧ ∀ v, cover (G v) = h (cover v) := by
  have hcover : cover (-1, -1) = (1, 1) := by simp [cover_apply]
  obtain ⟨G, hG₀, hG⟩ := (isCoveringMap_cover.existsUnique_continuousMap_lifts
    ((h : C(Circle × Circle, Circle × Circle)).comp cover) (-1, -1) (-1, -1)
    (by simp [hcover, h₁₁])).exists
  exact ⟨G, hG₀, fun v ↦ congrFun hG v⟩

/-! ### The lift of a homeomorphism fixing the coordinate circles -/

/-- The lift fixes the boundary of the square: on each line through a side of the square the
covering lands in a coordinate circle, where `h` is the identity, so the lift restricted to that
line is a lift of the covering and is the identity. -/
private theorem lift_apply_of_side {h : Circle × Circle ≃ₜ Circle × Circle}
    (h₁ : ∀ a, h (a, 1) = (a, 1)) (h₂ : ∀ b, h (1, b) = (1, b)) {G : C(ℝ × ℝ, ℝ × ℝ)}
    (hG₀ : G (-1, -1) = (-1, -1)) (hG : ∀ v, cover (G v) = h (cover v)) {v : ℝ × ℝ}
    (hv : v.1 = -1 ∨ v.1 = 1 ∨ v.2 = -1 ∨ v.2 = 1) : G v = v := by
  have hhor {c : ℝ} (hc : c = -1 ∨ c = 1) (x : ℝ) : cover (G (x, c)) = cover (x, c) := by
    have hc' : cover (x, c) = (Circle.exp (π * (x + 1)), 1) := by
      simp only [cover_apply, exp_pi_mul_add_one_eq_one hc]
    rw [hG, hc', h₁]
  have hver {c : ℝ} (hc : c = -1 ∨ c = 1) (y : ℝ) : cover (G (c, y)) = cover (c, y) := by
    have hc' : cover (c, y) = (1, Circle.exp (π * (y + 1))) := by
      simp only [cover_apply, exp_pi_mul_add_one_eq_one hc]
    rw [hG, hc', h₂]
  have hb (x : ℝ) : G (x, -1) = (x, -1) :=
    eq_of_cover_eq (F := fun x ↦ G (x, -1)) (by fun_prop) (by fun_prop) (hhor (.inl rfl))
      (a₀ := -1) hG₀ x
  have hl (y : ℝ) : G (-1, y) = (-1, y) :=
    eq_of_cover_eq (F := fun y ↦ G (-1, y)) (by fun_prop) (by fun_prop) (hver (.inl rfl))
      (a₀ := -1) hG₀ y
  have ht (x : ℝ) : G (x, 1) = (x, 1) :=
    eq_of_cover_eq (F := fun x ↦ G (x, 1)) (by fun_prop) (by fun_prop) (hhor (.inr rfl))
      (a₀ := -1) (hl 1) x
  have hr (y : ℝ) : G (1, y) = (1, y) :=
    eq_of_cover_eq (F := fun y ↦ G (1, y)) (by fun_prop) (by fun_prop) (hver (.inr rfl))
      (a₀ := -1) (hb 1) y
  obtain ⟨x, y⟩ := v
  rcases hv with rfl | rfl | rfl | rfl
  exacts [hl y, hr y, hb x, ht x]

/-- On the open square the coordinates of the lift avoid `±1`: there the covering avoids the
coordinate circles, and a point which `h` maps onto a coordinate circle is fixed by `h`, so it lies
on that circle already. -/
private theorem lift_ne_of_abs_lt_one {h : Circle × Circle ≃ₜ Circle × Circle}
    (h₁ : ∀ a, h (a, 1) = (a, 1)) (h₂ : ∀ b, h (1, b) = (1, b)) {G : C(ℝ × ℝ, ℝ × ℝ)}
    (hG : ∀ v, cover (G v) = h (cover v)) {w : ℝ × ℝ} (hw₁ : |w.1| < 1) (hw₂ : |w.2| < 1) :
    ((G w).1 ≠ 1 ∧ (G w).1 ≠ -1) ∧ ((G w).2 ≠ 1 ∧ (G w).2 ≠ -1) := by
  have hcirc {w : Circle × Circle} (hw : (h w).1 = 1 ∨ (h w).2 = 1) : w.1 = 1 ∨ w.2 = 1 := by
    have hfix : h (h w) = h w := by
      rcases hw with hw | hw
      · have hw' : h w = (1, (h w).2) := Prod.ext hw rfl
        rw [hw', h₂]
      · have hw' : h w = ((h w).1, 1) := Prod.ext rfl hw
        rw [hw', h₁]
    rwa [h.injective hfix] at hw
  have hoff : ¬((h (cover w)).1 = 1 ∨ (h (cover w)).2 = 1) := fun hw ↦ by
    rcases hcirc hw with hc | hc
    exacts [exp_pi_mul_add_one_ne_one hw₁ hc, exp_pi_mul_add_one_ne_one hw₂ hc]
  rw [← hG, cover_apply] at hoff
  exact ⟨⟨fun he ↦ hoff (.inl (exp_pi_mul_add_one_eq_one (.inr he))),
    fun he ↦ hoff (.inl (exp_pi_mul_add_one_eq_one (.inl he)))⟩,
    ⟨fun he ↦ hoff (.inr (exp_pi_mul_add_one_eq_one (.inr he))),
    fun he ↦ hoff (.inr (exp_pi_mul_add_one_eq_one (.inl he)))⟩⟩

/-- The lift maps the open square into itself. Its first coordinate is `0` at the point `(0, -1)`
of the bottom side, which is fixed, and never `±1` on the preconnected set `(-1, 1) × [-1, 1)`, so
it stays in `(-1, 1)` there; similarly for the second coordinate on `[-1, 1) × (-1, 1)`. -/
private theorem abs_lift_lt_one {h : Circle × Circle ≃ₜ Circle × Circle}
    (h₁ : ∀ a, h (a, 1) = (a, 1)) (h₂ : ∀ b, h (1, b) = (1, b)) {G : C(ℝ × ℝ, ℝ × ℝ)}
    (hG₀ : G (-1, -1) = (-1, -1)) (hG : ∀ v, cover (G v) = h (cover v)) {v : ℝ × ℝ}
    (hv₁ : |v.1| < 1) (hv₂ : |v.2| < 1) : |(G v).1| < 1 ∧ |(G v).2| < 1 := by
  have hside {w : ℝ × ℝ} (hw : w.1 = -1 ∨ w.1 = 1 ∨ w.2 = -1 ∨ w.2 = 1) : G w = w :=
    lift_apply_of_side h₁ h₂ hG₀ hG hw
  have hne {w : ℝ × ℝ} (hw₁ : |w.1| < 1) (hw₂ : |w.2| < 1) :=
    lift_ne_of_abs_lt_one h₁ h₂ hG hw₁ hw₂
  have habs {x : ℝ} : |x| < 1 ↔ x ∈ Ioo (-1) 1 := abs_lt
  -- The intermediate value theorem: a continuous function on a preconnected set which never takes
  -- the values `±1`, and takes a value in `(-1, 1)` somewhere, stays in `(-1, 1)`.
  have hivt {s : Set (ℝ × ℝ)} (hs : IsPreconnected s) {f : ℝ × ℝ → ℝ} (hf : Continuous f)
      {a : ℝ × ℝ} (ha : a ∈ s) (hfa : |f a| < 1) (hne : ∀ x ∈ s, f x ≠ 1 ∧ f x ≠ -1) {x : ℝ × ℝ}
      (hx : x ∈ s) : |f x| < 1 := by
    obtain ⟨hfa₁, hfa₂⟩ := abs_lt.1 hfa
    refine abs_lt.2 ⟨lt_of_not_ge fun hle ↦ ?_, lt_of_not_ge fun hle ↦ ?_⟩
    · obtain ⟨y, hy, hfy⟩ := hs.intermediate_value hx ha hf.continuousOn ⟨hle, hfa₁.le⟩
      exact (hne y hy).2 hfy
    · obtain ⟨y, hy, hfy⟩ := hs.intermediate_value ha hx hf.continuousOn ⟨hfa₂.le, hle⟩
      exact (hne y hy).1 hfy
  constructor
  · refine hivt (s := Ioo (-1) 1 ×ˢ Ico (-1) 1)
      (isPreconnected_Ioo.prod isPreconnected_Ico) (f := fun w ↦ (G w).1) (by fun_prop)
      (a := (0, -1)) ⟨by simp, by simp⟩ (by rw [hside (.inr (.inr (.inl rfl)))]; simp)
      (fun w hw ↦ ?_) ⟨habs.1 hv₁, (habs.1 hv₂).1.le, (habs.1 hv₂).2⟩
    rcases eq_or_lt_of_le hw.2.1 with hw₂ | hw₂
    · rw [hside (.inr (.inr (.inl hw₂.symm)))]
      exact ⟨hw.1.2.ne, hw.1.1.ne'⟩
    · exact (hne (habs.2 hw.1) (habs.2 ⟨hw₂, hw.2.2⟩)).1
  · refine hivt (s := Ico (-1) 1 ×ˢ Ioo (-1) 1)
      (isPreconnected_Ico.prod isPreconnected_Ioo) (f := fun w ↦ (G w).2) (by fun_prop)
      (a := (-1, 0)) ⟨by simp, by simp⟩ (by rw [hside (.inl rfl)]; simp)
      (fun w hw ↦ ?_) ⟨⟨(habs.1 hv₁).1.le, (habs.1 hv₁).2⟩, habs.1 hv₂⟩
    rcases eq_or_lt_of_le hw.1.1 with hw₁ | hw₁
    · rw [hside (.inl hw₁.symm)]
      exact ⟨hw.2.2.ne, hw.2.1.ne'⟩
    · exact (hne (habs.2 ⟨hw₁, hw.1.2⟩) (habs.2 hw.2)).2

/-- **The lift of a homeomorphism fixing the coordinate circles.** It fixes the boundary of the
square `[-1, 1]²`, the unit sphere of `ℝ × ℝ` for the sup norm, and maps its interior into
itself. -/
private theorem exists_lift_of_apply_eq {h : Circle × Circle ≃ₜ Circle × Circle}
    (h₁ : ∀ a, h (a, 1) = (a, 1)) (h₂ : ∀ b, h (1, b) = (1, b)) :
    ∃ G : C(ℝ × ℝ, ℝ × ℝ), G (-1, -1) = (-1, -1) ∧ (∀ v, cover (G v) = h (cover v)) ∧
      (∀ v, ‖v‖ = 1 → G v = v) ∧ ∀ v, ‖v‖ < 1 → ‖G v‖ < 1 := by
  obtain ⟨G, hG₀, hG⟩ := exists_lift h (h₁ 1)
  refine ⟨G, hG₀, hG, fun v hv ↦ lift_apply_of_side h₁ h₂ hG₀ hG ?_, fun v hv ↦ ?_⟩
  · -- In the sup norm, a vector of norm `1` lies on the boundary of the square.
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hv
    rcases max_choice |v.1| |v.2| with hmax | hmax <;> rw [hmax, abs_eq zero_le_one] at hv <;>
      rcases hv with hv | hv <;> simp [hv]
  · rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff] at hv ⊢
    exact abs_lift_lt_one h₁ h₂ hG₀ hG hv.1 hv.2

/-- **A homeomorphism of the torus fixing the coordinate circles comes from the square.** It is
covered by a homeomorphism of the square `[-1, 1]²` fixing the boundary: the lift of `h`, whose
inverse is the lift of `h⁻¹`. -/
private theorem exists_homeomorph_closedBall {h : Circle × Circle ≃ₜ Circle × Circle}
    (h₁ : ∀ a, h (a, 1) = (a, 1)) (h₂ : ∀ b, h (1, b) = (1, b)) :
    ∃ f : closedBall (0 : ℝ × ℝ) 1 ≃ₜ closedBall (0 : ℝ × ℝ) 1,
      (∀ x : closedBall (0 : ℝ × ℝ) 1, ‖(x : ℝ × ℝ)‖ = 1 → f x = x) ∧
        ∀ x, cover (f x : ℝ × ℝ) = h (cover x) := by
  obtain ⟨G, hG₀, hG, hGs, hGb⟩ := exists_lift_of_apply_eq h₁ h₂
  obtain ⟨G', hG'₀, hG', -, hG'b⟩ := exists_lift_of_apply_eq (h := h.symm)
    (fun a ↦ h.symm_apply_eq.2 (h₁ a).symm) (fun b ↦ h.symm_apply_eq.2 (h₂ b).symm)
  -- The two lifts are inverse to each other, by uniqueness of lifts.
  have hinv₁ (v : ℝ × ℝ) : G (G' v) = v :=
    eq_of_cover_eq (F := fun v ↦ G (G' v)) (F' := id) (by fun_prop) continuous_id
      (fun v ↦ by rw [hG, hG', Homeomorph.apply_symm_apply, id]) (a₀ := (-1, -1))
      (by rw [hG'₀, hG₀, id]) v
  have hinv₂ (v : ℝ × ℝ) : G' (G v) = v :=
    eq_of_cover_eq (F := fun v ↦ G' (G v)) (F' := id) (by fun_prop) continuous_id
      (fun v ↦ by rw [hG', hG, Homeomorph.symm_apply_apply, id]) (a₀ := (-1, -1))
      (by rw [hG₀, hG'₀, id]) v
  -- A lift fixing the boundary and mapping the interior into itself maps the square into itself.
  have hmaps (g : C(ℝ × ℝ, ℝ × ℝ)) (hgs : ∀ v, ‖v‖ = 1 → g v = v)
      (hgb : ∀ v, ‖v‖ < 1 → ‖g v‖ < 1) (x : closedBall (0 : ℝ × ℝ) 1) :
      g x ∈ closedBall (0 : ℝ × ℝ) 1 := by
    rw [mem_closedBall_zero_iff]
    rcases (mem_closedBall_zero_iff.1 x.2).lt_or_eq with hx | hx
    · exact (hgb x hx).le
    · rw [hgs x hx, hx]
  have hGs' (v : ℝ × ℝ) (hv : ‖v‖ = 1) : G' v = v := by
    conv_lhs => rw [← hGs v hv]
    exact hinv₂ v
  refine ⟨{ toFun := fun x ↦ ⟨G x, hmaps G hGs hGb x⟩
            invFun := fun x ↦ ⟨G' x, hmaps G' hGs' hG'b x⟩
            left_inv := fun x ↦ Subtype.ext (hinv₂ x)
            right_inv := fun x ↦ Subtype.ext (hinv₁ x)
            continuous_toFun := by fun_prop
            continuous_invFun := by fun_prop }, fun x hx ↦ Subtype.ext (hGs x hx), fun x ↦ hG x⟩

/-! ### Descending isotopies of the square to the torus -/

/-- The covering maps the square onto the torus. -/
private theorem exists_mem_closedBall_cover_eq (w : Circle × Circle) :
    ∃ x : closedBall (0 : ℝ × ℝ) 1, cover x = w := by
  have hcoord (z : Circle) : ∃ x : ℝ, |x| ≤ 1 ∧ Circle.exp (π * (x + 1)) = z := by
    obtain ⟨θ, ⟨hθ₁, hθ₂⟩, rfl⟩ := Circle.surjOn_exp_neg_pi_pi (mem_univ z)
    rcases le_or_gt 0 θ with hθ | hθ
    · refine ⟨θ / π - 1, abs_le.2 ⟨?_, ?_⟩, ?_⟩
      · rw [le_sub_iff_add_le, neg_add_cancel]; positivity
      · rw [sub_le_iff_le_add, div_le_iff₀ pi_pos]; linarith
      · congr 1; field_simp; ring
    · refine ⟨θ / π + 1, abs_le.2 ⟨?_, ?_⟩, ?_⟩
      · rw [← sub_le_iff_le_add, le_div_iff₀ pi_pos]; linarith
      · rw [← le_sub_iff_add_le, sub_self, div_nonpos_iff]; right; exact ⟨hθ.le, pi_pos.le⟩
      · rw [show π * (θ / π + 1 + 1) = θ + 2 * π by field_simp; ring, Circle.exp_add_two_pi]
  obtain ⟨x, hx, hxw⟩ := hcoord w.1
  obtain ⟨y, hy, hyw⟩ := hcoord w.2
  refine ⟨⟨(x, y), ?_⟩, Prod.ext hxw hyw⟩
  rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le hx hy

/-- Two distinct points of the square with the same image in the torus both lie on the boundary of
the square. -/
private theorem norm_eq_one_of_cover_eq {x y : ℝ × ℝ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hxy : cover x = cover y) (hne : x ≠ y) : ‖x‖ = 1 ∧ ‖y‖ = 1 := by
  -- In each coordinate the two points differ by an even integer, at most `2` in absolute value.
  have hcoord {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
      (hab : Circle.exp (π * (a + 1)) = Circle.exp (π * (b + 1))) (hne : a ≠ b) :
      |a| = 1 ∧ |b| = 1 := by
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 hab
    have hm' : a = b + 2 * m := by
      have := mul_left_cancel₀ pi_ne_zero (show π * (a + 1) = π * (b + 1 + 2 * m) by linarith)
      linarith
    obtain ⟨ha₁, ha₂⟩ := abs_le.1 ha
    obtain ⟨hb₁, hb₂⟩ := abs_le.1 hb
    have hm₁ : m ≤ 1 := by exact_mod_cast (show (m : ℝ) ≤ 1 by linarith)
    have hm₂ : -1 ≤ m := by exact_mod_cast (show (-1 : ℝ) ≤ m by linarith)
    have hm₀ : m ≠ 0 := by rintro rfl; exact hne (by simpa using hm')
    rcases (show m = -1 ∨ m = 1 by omega) with rfl | rfl
    · push_cast at hm'
      exact ⟨by rw [abs_eq zero_le_one]; right; linarith,
        by rw [abs_eq zero_le_one]; left; linarith⟩
    · push_cast at hm'
      exact ⟨by rw [abs_eq zero_le_one]; left; linarith,
        by rw [abs_eq zero_le_one]; right; linarith⟩
  have hnorm {v : ℝ × ℝ} (hv : ‖v‖ ≤ 1) {c : ℝ} (hc : |c| = 1) (hcv : c = v.1 ∨ c = v.2) :
      ‖v‖ = 1 := by
    refine le_antisymm hv ?_
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, ← hc]
    rcases hcv with rfl | rfl
    exacts [le_max_left _ _, le_max_right _ _]
  have habs {v : ℝ × ℝ} (hv : ‖v‖ ≤ 1) : |v.1| ≤ 1 ∧ |v.2| ≤ 1 := by
    rwa [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff] at hv
  by_cases h₁ : x.1 = y.1
  · have h₂ : x.2 ≠ y.2 := fun h₂ ↦ hne (Prod.ext h₁ h₂)
    obtain ⟨hx₂, hy₂⟩ := hcoord (habs hx).2 (habs hy).2 (congrArg Prod.snd hxy) h₂
    exact ⟨hnorm hx hx₂ (.inr rfl), hnorm hy hy₂ (.inr rfl)⟩
  · obtain ⟨hx₁, hy₁⟩ := hcoord (habs hx).1 (habs hy).1 (congrArg Prod.fst hxy) h₁
    exact ⟨hnorm hx hx₁ (.inl rfl), hnorm hy hy₁ (.inl rfl)⟩

/-- A point of the square lying over a coordinate circle lies on the boundary of the square. -/
private theorem norm_eq_one_of_cover {x : ℝ × ℝ} (hx : ‖x‖ ≤ 1)
    (hcx : (cover x).1 = 1 ∨ (cover x).2 = 1) : ‖x‖ = 1 := by
  refine hx.antisymm (le_of_not_gt fun hlt ↦ ?_)
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff] at hlt
  rcases hcx with h₁ | h₂
  exacts [exp_pi_mul_add_one_ne_one hlt.1 h₁, exp_pi_mul_add_one_ne_one hlt.2 h₂]

/-- An isotopy of the square fixing its boundary keeps two points of the square over the same point
of the torus exactly when they started there: distinct such points lie on the boundary, which is
fixed, and the boundary is preserved by every slice. -/
private theorem cover_apply_eq_cover_apply_iff
    {A : AmbientIsotopy (closedBall (0 : ℝ × ℝ) 1)}
    (hA : ∀ t (x : closedBall (0 : ℝ × ℝ) 1), ‖(x : ℝ × ℝ)‖ = 1 → A.toContinuousMap (t, x) = x)
    {t : I} {x y : closedBall (0 : ℝ × ℝ) 1} :
    cover (A.toContinuousMap (t, x)) = cover (A.toContinuousMap (t, y)) ↔ cover x = cover y := by
  have hB (z : closedBall (0 : ℝ × ℝ) 1) : ‖(z : ℝ × ℝ)‖ ≤ 1 := mem_closedBall_zero_iff.1 z.2
  have hAs {z : closedBall (0 : ℝ × ℝ) 1} (hz : ‖(A.toContinuousMap (t, z) : ℝ × ℝ)‖ = 1) :
      ‖(z : ℝ × ℝ)‖ = 1 := by
    rwa [← (A.isHomeomorph_apply t).injective (hA t _ hz)]
  constructor
  · intro hxy
    by_cases hne : (A.toContinuousMap (t, x) : ℝ × ℝ) = A.toContinuousMap (t, y)
    · rw [(A.isHomeomorph_apply t).injective (Subtype.ext hne)]
    · obtain ⟨hx, hy⟩ := norm_eq_one_of_cover_eq (hB _) (hB _) hxy hne
      rwa [hA t x (hAs hx), hA t y (hAs hy)] at hxy
  · intro hxy
    by_cases hne : (x : ℝ × ℝ) = y
    · rw [Subtype.ext hne]
    · obtain ⟨hx, hy⟩ := norm_eq_one_of_cover_eq (hB x) (hB y) hxy hne
      rw [hA t x hx, hA t y hy, hxy]

/-- **An isotopy of the square fixing its boundary descends to the torus**, along the quotient map
`[0, 1] × [-1, 1]² → [0, 1] × (S¹ × S¹)` from a compact space to a Hausdorff space. Its
level-preserving total map is a continuous bijection of a compact Hausdorff space, hence a
homeomorphism. -/
private theorem exists_ambientIsotopy_cover_eq (A : AmbientIsotopy (closedBall (0 : ℝ × ℝ) 1))
    (hA : ∀ t (x : closedBall (0 : ℝ × ℝ) 1), ‖(x : ℝ × ℝ)‖ = 1 → A.toContinuousMap (t, x) = x) :
    ∃ Φ : AmbientIsotopy (Circle × Circle),
      ∀ t (x : closedBall (0 : ℝ × ℝ) 1), Φ.toContinuousMap (t, cover x) =
        cover (A.toContinuousMap (t, x)) := by
  let B := closedBall (0 : ℝ × ℝ) 1
  let Q : C(I × B, I × (Circle × Circle)) := ⟨fun p ↦ (p.1, cover p.2), by fun_prop⟩
  have hQ : Topology.IsQuotientMap Q := .of_surjective_continuous (fun p ↦
    let ⟨x, hx⟩ := exists_mem_closedBall_cover_eq p.2; ⟨(p.1, x), Prod.ext rfl hx⟩) Q.continuous
  let Ψ₀ : C(I × B, Circle × Circle) := ⟨fun p ↦ cover (A.toContinuousMap p), by fun_prop⟩
  have hΨ₀ : FactorsThrough Ψ₀ Q := by
    rintro ⟨t, x⟩ ⟨t', y⟩ hxy
    obtain ⟨rfl, hxy⟩ := Prod.mk.inj hxy
    exact (cover_apply_eq_cover_apply_iff hA).2 hxy
  let Ψ := hQ.lift Ψ₀ hΨ₀
  have hΨ (t : I) (x : B) : Ψ (t, cover x) = cover (A.toContinuousMap (t, x)) :=
    DFunLike.congr_fun (hQ.lift_comp Ψ₀ hΨ₀) (t, x)
  refine ⟨{ toContinuousMap := Ψ, isHomeomorph_total' := ?_, map_zero_left' := fun w ↦ ?_ }, hΨ⟩
  · refine isHomeomorph_iff_continuous_bijective.2 ⟨continuous_fst.prodMk Ψ.continuous, ?_, ?_⟩
    · rintro ⟨t, w⟩ ⟨t', w'⟩ hww'
      obtain ⟨rfl, hww'⟩ := Prod.mk.inj hww'
      obtain ⟨x, rfl⟩ := exists_mem_closedBall_cover_eq w
      obtain ⟨y, rfl⟩ := exists_mem_closedBall_cover_eq w'
      simp only [ContinuousMap.toFun_eq_coe, hΨ] at hww'
      exact Prod.ext rfl ((cover_apply_eq_cover_apply_iff hA).1 hww')
    · rintro ⟨t, w⟩
      obtain ⟨y, rfl⟩ := exists_mem_closedBall_cover_eq w
      obtain ⟨x, rfl⟩ := (A.isHomeomorph_apply t).surjective y
      exact ⟨(t, cover x), by simp only [ContinuousMap.toFun_eq_coe, hΨ]⟩
  · obtain ⟨x, rfl⟩ := exists_mem_closedBall_cover_eq w
    simp only [ContinuousMap.toFun_eq_coe, hΨ, AmbientIsotopy.map_zero_left]

end TauCeti.TorusIsotopy

open TauCeti TauCeti.TorusIsotopy

namespace Homeomorph

/-- **A homeomorphism of the torus fixing the two coordinate circles is isotopic to the
identity.** If a homeomorphism `h` of `S¹ × S¹` fixes every point of `S¹ × {1}` and of `{1} × S¹`,
it is the end of an ambient isotopy of the torus fixing those two circles at every time. -/
theorem exists_ambientIsotopy_final_eq_of_apply_mk_one_eq (h : Circle × Circle ≃ₜ Circle × Circle)
    (h₁ : ∀ a, h (a, 1) = (a, 1)) (h₂ : ∀ b, h (1, b) = (1, b)) :
    ∃ Φ : AmbientIsotopy (Circle × Circle), Φ.final = h ∧
      ∀ t a, Φ.toContinuousMap (t, (a, 1)) = (a, 1) ∧ Φ.toContinuousMap (t, (1, a)) = (1, a) := by
  obtain ⟨f, hf, hfh⟩ := exists_homeomorph_closedBall h₁ h₂
  obtain ⟨Φ, hΦ⟩ := exists_ambientIsotopy_cover_eq (f.alexanderIsotopyClosedBall hf)
    (f.alexanderIsotopyClosedBall_apply_of_norm_eq_one hf)
  -- A point of a coordinate circle is the image of a point on the boundary of the square, which
  -- the isotopy fixes.
  have hfix {w : Circle × Circle} (hw : w.1 = 1 ∨ w.2 = 1) (t : I) :
      Φ.toContinuousMap (t, w) = w := by
    obtain ⟨x, rfl⟩ := exists_mem_closedBall_cover_eq w
    rw [hΦ, f.alexanderIsotopyClosedBall_apply_of_norm_eq_one hf t x
      (norm_eq_one_of_cover (mem_closedBall_zero_iff.1 x.2) hw)]
  refine ⟨Φ, ContinuousMap.ext fun w ↦ ?_, fun t a ↦ ⟨hfix (.inr rfl) t, hfix (.inl rfl) t⟩⟩
  obtain ⟨x, rfl⟩ := exists_mem_closedBall_cover_eq w
  rw [AmbientIsotopy.final_apply, hΦ, ← AmbientIsotopy.final_apply,
    alexanderIsotopyClosedBall_final, hfh, ContinuousMap.coe_ofClass]

/-- **Homeomorphisms of the torus agreeing on the two coordinate circles are isotopic.** -/
theorem isotopic_of_apply_mk_one_eq (g k : Circle × Circle ≃ₜ Circle × Circle)
    (h₁ : ∀ a, g (a, 1) = k (a, 1)) (h₂ : ∀ b, g (1, b) = k (1, b)) :
    Isotopic (g : C(Circle × Circle, Circle × Circle)) k := by
  obtain ⟨Φ, hΦ, -⟩ := exists_ambientIsotopy_final_eq_of_apply_mk_one_eq (k.trans g.symm)
    (fun a ↦ by rw [trans_apply, ← h₁, symm_apply_apply])
    (fun b ↦ by rw [trans_apply, ← h₂, symm_apply_apply])
  have := (Φ.isotopic (f := ContinuousMap.id _) Topology.IsEmbedding.id).postcomp_homeomorph g
  have hk : (g : C(Circle × Circle, Circle × Circle)).comp
      ((k.trans g.symm : C(Circle × Circle, Circle × Circle)).comp (ContinuousMap.id _)) = k :=
    ContinuousMap.ext fun w ↦ by simp
  rwa [hΦ, hk, ContinuousMap.comp_id] at this

end Homeomorph
