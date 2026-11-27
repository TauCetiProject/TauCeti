/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.LinearAlgebra.Reflection
public import TauCeti.RepresentationTheory.OrbitSpace
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Order.Filter.Finite
import Mathlib.RepresentationTheory.Stabilizer
import TauCeti.LinearAlgebra.Reflection

/-!
# Closed chambers as strict fundamental domains

Let `α i`, for `i` in a finite type, be linear forms on a real vector space `V`, cutting `V` by the
hyperplanes `ker α i`. For a point `x₀`, the **closed chamber** `TauCeti.closedChamber α x₀` is
the set of `x` lying weakly on the same side as `x₀` of every hyperplane,
`0 ≤ α i x * α i x₀`, and the **open chamber** `TauCeti.openChamber α x₀` is cut out by the strict
inequalities. A point is **regular** when it lies on no hyperplane; the open chamber of a regular
point is the set of regular points of its closed chamber.

Let `ρ` be a representation of a finite group `G` on `V` such that

* for every `i` some `ρ g` is the reflection `x ↦ x - α i x • c` along a coroot `c` with
  `α i c = 2` that is orthogonal to `ker α i` for a positive definite bilinear form `B`, and
* only the identity fixes a regular point.

This is the situation of the Weyl group of a maximal torus of a compact connected Lie group acting
on the Lie algebra of the torus, with the real roots as the forms. For a regular `x₀`, the closed
chamber of `x₀` is then a **strict fundamental domain**: every orbit meets it in exactly one point
(`Representation.existsUnique_mem_closedChamber_orbitRel`). For a topology on `V` in which every
`ρ g` and every `α i` is continuous, the inclusion of the closed chamber therefore induces a
homeomorphism onto the orbit space `V / G` (`Representation.closedChamberHomeomorph`).

The three steps are these.

* **Existence** (`Representation.exists_apply_mem_closedChamber`). Choose `g` maximizing the
  height `B (x₀, ρ g x)`. If `ρ g x` were strictly on the wrong side of `ker α i`, reflecting it
  would raise the height by a positive multiple of `-α i (ρ g x) α i x₀`. Neither `x₀` regular nor
  the freeness hypothesis is needed here.
* **Freeness on open chambers** (`Representation.eq_one_of_apply_mem_openChamber`). Every `ρ g`
  preserves the regular points: if `ρ g x` lay on `ker α i`, the reflection in that hyperplane would
  fix it, and a conjugate of the reflection would fix `x`. A segment of an open chamber consists of
  regular points, so `ρ g` maps an open chamber that it moves into itself onto that open chamber.
  The sum of the `⟨g⟩`-orbit of a point of the chamber is then a regular point fixed by `g`.
* **Uniqueness on the closed chamber**
  (`Representation.apply_eq_self_of_apply_mem_closedChamber`). Let `x` and `y = ρ g x` both lie in
  the closed chamber. Applying existence to the stabilizer of `y`, which contains the reflections in
  the walls through `y`, gives `h` fixing `y` with `ρ (h g) x₀` on the side of `x₀` of those walls.
  For small `t > 0`, `ρ (h g)` maps the regular point `x + t x₀` of the open chamber to
  `y + t ρ (h g) x₀`, which lies in the open chamber again. So `h g = 1` by freeness, and `g` fixes
  `y`, hence `y = x`.

No root system structure is used: the forms need not be permuted by `G`, and no base or positive
system is chosen. Compare `Representation.chamber`, the open chambers of the reflecting hyperplanes
of a finite orthogonal group on an inner product space, and
`TauCeti.existsUnique_mem_orbit_inter_dominantChamber`, the dominant chamber of a crystallographic
root system.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Springer (2002), Ch. V, § 3.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  § 1.12.
-/

public section

open Filter Topology

namespace TauCeti

variable {ι V : Type*} [AddCommGroup V] [Module ℝ V] {α : ι → Module.Dual ℝ V} {x₀ x y : V}

/-- The **closed chamber** of `x₀` for the hyperplanes `ker α i`: the points lying weakly on the
same side as `x₀` of every hyperplane. -/
def closedChamber (α : ι → Module.Dual ℝ V) (x₀ : V) : Set V :=
  {x | ∀ i, 0 ≤ α i x * α i x₀}

/-- The **open chamber** of `x₀` for the hyperplanes `ker α i`: the points lying strictly on the
same side as `x₀` of every hyperplane. It is empty unless `x₀` lies on no hyperplane. -/
def openChamber (α : ι → Module.Dual ℝ V) (x₀ : V) : Set V :=
  {x | ∀ i, 0 < α i x * α i x₀}

@[simp]
theorem mem_closedChamber : x ∈ closedChamber α x₀ ↔ ∀ i, 0 ≤ α i x * α i x₀ :=
  Iff.rfl

@[simp]
theorem mem_openChamber : x ∈ openChamber α x₀ ↔ ∀ i, 0 < α i x * α i x₀ :=
  Iff.rfl

theorem openChamber_subset_closedChamber : openChamber α x₀ ⊆ closedChamber α x₀ :=
  fun _ hx i ↦ (hx i).le

/-- A point of the open chamber lies on no hyperplane. -/
theorem apply_ne_zero_of_mem_openChamber (hx : x ∈ openChamber α x₀) (i : ι) : α i x ≠ 0 :=
  fun h ↦ by simpa [h] using hx i

/-- A nonempty open chamber has a base point lying on no hyperplane. -/
theorem apply_ne_zero_of_mem_openChamber_base (hx : x ∈ openChamber α x₀) (i : ι) : α i x₀ ≠ 0 :=
  fun h ↦ by simpa [h] using hx i

/-- A point lies in its own open chamber exactly when it lies on no hyperplane. -/
theorem self_mem_openChamber_iff : x₀ ∈ openChamber α x₀ ↔ ∀ i, α i x₀ ≠ 0 :=
  forall_congr' fun _ ↦ mul_self_pos

/-- The open chamber consists of the points of the closed chamber lying on no hyperplane. -/
theorem mem_openChamber_iff_of_mem_closedChamber (hx : x ∈ closedChamber α x₀)
    (hx₀ : ∀ i, α i x₀ ≠ 0) : x ∈ openChamber α x₀ ↔ ∀ i, α i x ≠ 0 :=
  ⟨apply_ne_zero_of_mem_openChamber, fun h i ↦ (hx i).lt_of_ne (mul_ne_zero (h i) (hx₀ i)).symm⟩

/-- The open chamber is closed under addition. -/
theorem add_mem_openChamber (hx : x ∈ openChamber α x₀) (hy : y ∈ openChamber α x₀) :
    x + y ∈ openChamber α x₀ := fun i ↦ by
  rw [map_add, add_mul]
  exact add_pos (hx i) (hy i)

/-- The open chamber is convex. -/
theorem convex_openChamber : Convex ℝ (openChamber α x₀) := by
  intro x hx y hy a b ha hb hab i
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, add_mul, mul_assoc, mul_assoc]
  rcases ha.lt_or_eq with ha | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos ha (hx i)) (mul_nonneg hb (hy i).le)
  · rw [zero_add] at hab
    simpa [hab] using hy i

/-- The closed chamber is convex. -/
theorem convex_closedChamber : Convex ℝ (closedChamber α x₀) := by
  intro x hx y hy a b ha hb _ i
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, add_mul, mul_assoc, mul_assoc]
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

/-- Moving a point of the closed chamber towards `x₀` enters the open chamber. -/
theorem add_smul_mem_openChamber (hx : x ∈ closedChamber α x₀) (hx₀ : ∀ i, α i x₀ ≠ 0) {t : ℝ}
    (ht : 0 < t) : x + t • x₀ ∈ openChamber α x₀ := fun i ↦ by
  rw [map_add, map_smul, smul_eq_mul, add_mul, mul_assoc]
  exact add_pos_of_nonneg_of_pos (hx i) (mul_pos ht (mul_self_pos.2 (hx₀ i)))

/-- The closed chamber is closed when the forms are continuous. -/
theorem isClosed_closedChamber [TopologicalSpace V] (hα : ∀ i, Continuous (α i)) :
    IsClosed (closedChamber α x₀) := by
  simp only [closedChamber, Set.ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le continuous_const ((hα i).mul continuous_const)

/-- The open chamber is open when there are finitely many forms and they are continuous. -/
theorem isOpen_openChamber [Finite ι] [TopologicalSpace V] (hα : ∀ i, Continuous (α i)) :
    IsOpen (openChamber α x₀) := by
  simp only [openChamber, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const ((hα i).mul continuous_const)

/-- The closure of the open chamber of a regular point is its closed chamber, for continuous
forms on a topological vector space. -/
theorem closure_openChamber [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]
    (hα : ∀ i, Continuous (α i)) (hx₀ : ∀ i, α i x₀ ≠ 0) :
    closure (openChamber α x₀) = closedChamber α x₀ := by
  refine (closure_minimal openChamber_subset_closedChamber (isClosed_closedChamber hα)).antisymm
    fun x hx ↦ ?_
  -- The points `x + t • x₀`, `t > 0`, of the open chamber tend to `x`.
  have h : Tendsto (fun t : ℝ ↦ x + t • x₀) (𝓝[>] 0) (𝓝 x) := by
    have hc : Continuous fun t : ℝ ↦ x + t • x₀ := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto h (eventually_nhdsWithin_of_forall fun t ht ↦
    add_smul_mem_openChamber hx hx₀ ht)

/-- A point `y` of the closed chamber of a regular `x₀` moves into the closed chamber in every
direction `v` lying on the side of `x₀` of the walls through `y`, for small positive times. -/
private theorem exists_pos_add_smul_mem_closedChamber [Finite ι] {y v : V}
    (hy : y ∈ closedChamber α x₀) (hx₀ : ∀ i, α i x₀ ≠ 0)
    (hv : ∀ i ∈ {i | α i y = 0}, 0 ≤ α i v * α i x₀) :
    ∃ t : ℝ, 0 < t ∧ y + t • v ∈ closedChamber α x₀ := by
  -- Off the walls through `y`, the strict inequalities persist for small `t`.
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, α i y ≠ 0 → 0 < α i y * α i x₀ + t * (α i v * α i x₀) :=
    eventually_all.2 fun i ↦ by
      by_cases hi : α i y = 0
      · exact Eventually.of_forall fun _ h ↦ absurd hi h
      · have h0 : 0 < α i y * α i x₀ := (hy i).lt_of_ne (mul_ne_zero hi (hx₀ i)).symm
        have hc : Continuous fun t : ℝ ↦ α i y * α i x₀ + t * (α i v * α i x₀) := by fun_prop
        exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using h0)) |>.mono fun _ ht _ ↦ ht
  obtain ⟨t, ht, ht0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  refine ⟨t, ht0, fun i ↦ ?_⟩
  rw [map_add, map_smul, smul_eq_mul, add_mul, mul_assoc]
  by_cases hi : α i y = 0
  · rw [hi, zero_mul, zero_add]
    exact mul_nonneg (le_of_lt (Set.mem_Ioi.1 ht0)) (hv i hi)
  · exact (ht i hi).le

end TauCeti

namespace Representation

open TauCeti

variable {ι G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V] (ρ : Representation ℝ G V)
  {α : ι → Module.Dual ℝ V} {B : LinearMap.BilinForm ℝ V} {x₀ : V}

/-! ### Existence of a representative in the closed chamber -/

/-- **Existence inside a subgroup.** If a subgroup `H` of a finite group contains the
`B`-orthogonal reflections in the walls `ker α i` for `i ∈ S`, then every `H`-orbit has a point on
the side of `x₀` of each of these walls. -/
private theorem exists_mem_forall_mem_le_mul [Finite G] (hB : ∀ v, v ≠ 0 → 0 < B v v)
    (H : Subgroup G) (S : Set ι)
    (hrefl : ∀ i ∈ S, ∃ (c : V) (hc : α i c = 2), (∀ x, α i x = 0 → B x c = 0) ∧
      ∃ g ∈ H, ρ g = (Module.reflection hc).toLinearMap)
    (x₀ x : V) : ∃ h ∈ H, ∀ i ∈ S, 0 ≤ α i (ρ h x) * α i x₀ := by
  -- Choose `h ∈ H` maximizing the height `B (x₀, ρ h x)`.
  obtain ⟨h, hH, hmax⟩ := Set.exists_max_image (H : Set G) (fun h ↦ B x₀ (ρ h x))
    (Set.toFinite _) ⟨1, H.one_mem⟩
  refine ⟨h, hH, fun i hi ↦ not_lt.1 fun hneg ↦ ?_⟩
  obtain ⟨c, hc, horth, g, hgH, hg⟩ := hrefl i hi
  have hcc : 0 < B c c := hB c fun h0 ↦ by simp [h0] at hc
  -- Reflecting `ρ h x` in `ker α i` would raise the height.
  have hle := hmax (g * h) (H.mul_mem hgH hH)
  rw [map_mul, mul_apply_eq_comp, hg, LinearEquiv.coe_coe,
    Module.bilinForm_apply_reflection_right hc horth] at hle
  nlinarith [mul_pos (neg_pos.2 hneg) hcc]

/-- **Every orbit meets the closed chamber.** Let `ρ` be a representation of a finite group
containing, for every `i`, the reflection in `ker α i` along a coroot orthogonal to `ker α i` for
a positive definite form `B`. Then for every `x₀` and `x`, some `ρ g x` lies in the closed chamber
of `x₀`. -/
theorem exists_apply_mem_closedChamber [Finite G] (hB : ∀ v, v ≠ 0 → 0 < B v v)
    (hrefl : ∀ i, ∃ (c : V) (hc : α i c = 2), (∀ x, α i x = 0 → B x c = 0) ∧
      ∃ g, ρ g = (Module.reflection hc).toLinearMap)
    (x₀ x : V) : ∃ g, ρ g x ∈ closedChamber α x₀ := by
  obtain ⟨g, -, hg⟩ := ρ.exists_mem_forall_mem_le_mul hB ⊤ Set.univ (fun i _ ↦ by
    obtain ⟨c, hc, horth, g, hg⟩ := hrefl i
    exact ⟨c, hc, horth, g, Subgroup.mem_top g, hg⟩) x₀ x
  exact ⟨g, fun i ↦ hg i (Set.mem_univ i)⟩

/-! ### Freeness on the open chambers -/

/-- **The group preserves the regular points.** If `ρ` contains the reflection in every
hyperplane `ker α i` and only the identity fixes a regular point, then `ρ g` maps regular points to
regular points. -/
theorem apply_ne_zero_of_forall_apply_ne_zero
    (hrefl : ∀ i, ∃ (c : V) (hc : α i c = 2), ∃ g, ρ g = (Module.reflection hc).toLinearMap)
    (hfree : ∀ g x, (∀ i, α i x ≠ 0) → ρ g x = x → g = 1) (g : G) {x : V}
    (hx : ∀ i, α i x ≠ 0) (i : ι) : α i (ρ g x) ≠ 0 := by
  intro h0
  obtain ⟨c, hc, s, hs⟩ := hrefl i
  -- The reflection `s` fixes `ρ g x`, so its conjugate `g⁻¹ s g` fixes the regular point `x`.
  have hfix : ρ (g⁻¹ * s * g) x = x := by
    simp [hs, Module.reflection_apply, h0]
  have hs1 : s = 1 := by
    have := hfree _ x hx hfix
    rwa [mul_assoc, inv_mul_eq_one, eq_comm, mul_eq_right] at this
  -- But the reflection sends the coroot `c ≠ 0` to `-c`.
  have hc' := congrArg (· c) hs
  simp only [hs1, map_one, one_apply_eq_self, LinearEquiv.coe_coe,
    Module.reflection_apply_self] at hc'
  have h2 := congrArg (α i) hc'
  rw [map_neg, hc] at h2
  norm_num at h2

/-- A map preserving the regular points and moving one point of an open chamber into that open
chamber maps the whole open chamber into itself: on a segment between two points of the open
chamber, a form changing sign would vanish somewhere. -/
private theorem apply_mem_openChamber_of_apply_mem_openChamber (f : V →ₗ[ℝ] V)
    (hf : ∀ x, (∀ i, α i x ≠ 0) → ∀ i, α i (f x) ≠ 0) {z y : V} (hz : z ∈ openChamber α x₀)
    (hfz : f z ∈ openChamber α x₀) (hy : y ∈ openChamber α x₀) : f y ∈ openChamber α x₀ := by
  intro i
  refine not_le.1 fun hle ↦ ?_
  set a := α i (f z) * α i x₀
  set b := α i (f y) * α i x₀
  have ha : 0 < a := hfz i
  have hb : b < 0 := hle.lt_of_ne fun h ↦ (mul_ne_zero
    (hf y (fun _ ↦ apply_ne_zero_of_mem_openChamber hy _) i)
    (apply_ne_zero_of_mem_openChamber_base hz i)) h
  -- The point `p = (1 - s) z + s y` of the open chamber, `s = a / (a - b)`, has `α i (f p) = 0`.
  have hab : 0 < a - b := by linarith
  set s := a / (a - b)
  have hs0 : 0 ≤ s := div_nonneg ha.le hab.le
  have hs1 : s ≤ 1 := (div_le_one hab).2 (by linarith)
  have hp := convex_openChamber hz hy (sub_nonneg.2 hs1) hs0 (sub_add_cancel 1 s)
  refine hf _ (fun _ ↦ apply_ne_zero_of_mem_openChamber hp _) i ?_
  have hval : α i (f ((1 - s) • z + s • y)) * α i x₀ = (1 - s) * a + s * b := by
    simp only [map_add, map_smul, smul_eq_mul, a, b]
    ring
  have hzero : (1 - s) * a + s * b = 0 := by
    simp only [s]
    field_simp
    ring
  rw [hzero] at hval
  exact (mul_eq_zero.1 hval).resolve_right (apply_ne_zero_of_mem_openChamber_base hz i)

/-- **Only the identity moves a point of an open chamber into that open chamber.** Let `ρ` be a
representation of a finite group containing the reflection in every hyperplane `ker α i`, such
that only the identity fixes a regular point. If `z` and `ρ g z` lie in the open chamber of `x₀`,
then `g = 1`. -/
theorem eq_one_of_apply_mem_openChamber [Finite G]
    (hrefl : ∀ i, ∃ (c : V) (hc : α i c = 2), ∃ g, ρ g = (Module.reflection hc).toLinearMap)
    (hfree : ∀ g x, (∀ i, α i x ≠ 0) → ρ g x = x → g = 1) {g : G} {z : V}
    (hz : z ∈ openChamber α x₀) (hgz : ρ g z ∈ openChamber α x₀) : g = 1 := by
  have hreg := ρ.apply_ne_zero_of_forall_apply_ne_zero hrefl hfree
  -- Every power of `g` maps `z` into the open chamber.
  have hpow (k : ℕ) : ρ (g ^ k) z ∈ openChamber α x₀ := by
    induction k with
    | zero => simpa using hz
    | succ k ih =>
      rw [pow_succ', map_mul, mul_apply_eq_comp]
      exact apply_mem_openChamber_of_apply_mem_openChamber (ρ g) (fun x hx ↦ hreg g hx) hz hgz ih
  -- The sum of the `⟨g⟩`-orbit of `z` is a regular point fixed by `g`.
  set n := orderOf g
  have hn : 0 < n := (isOfFinOrder_of_finite g).orderOf_pos
  set p := ∑ k ∈ Finset.range n, ρ (g ^ k) z
  have hsum (m : ℕ) : ∑ k ∈ Finset.range (m + 1), ρ (g ^ k) z ∈ openChamber α x₀ := by
    induction m with
    | zero => simpa using hpow 0
    | succ m ih => rw [Finset.sum_range_succ]; exact add_mem_openChamber ih (hpow _)
  have hp : p ∈ openChamber α x₀ := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simpa only [p, hm] using hsum m
  -- Applying `ρ g` shifts the index of the sum by one. The term `ρ (g ^ n) z` gained equals the
  -- term `ρ (g ^ 0) z` lost, because `g ^ n = 1 = g ^ 0`.
  have hfix : ρ g p = p := by
    have h := (Finset.sum_range_succ' (fun k ↦ ρ (g ^ k) z) n).symm.trans
      (Finset.sum_range_succ _ n)
    rw [pow_orderOf_eq_one, pow_zero, add_left_inj] at h
    simpa only [p, map_sum, ← mul_apply_eq_comp, ← map_mul, ← pow_succ'] using h
  exact hfree g p (fun _ ↦ apply_ne_zero_of_mem_openChamber hp _) hfix

/-! ### Uniqueness of the representative in the closed chamber -/

/-- **A group element moving a point of the closed chamber into the closed chamber fixes it.** Let
`ρ` be a representation of a finite group containing, for every `i`, the reflection in `ker α i`
along a coroot orthogonal to `ker α i` for a positive definite form `B`, and such that only the
identity fixes a regular point. If `x₀` is regular and `x` and `ρ g x` lie in the closed chamber of
`x₀`, then `ρ g x = x`. -/
theorem apply_eq_self_of_apply_mem_closedChamber [Finite G] [Finite ι]
    (hB : ∀ v, v ≠ 0 → 0 < B v v)
    (hrefl : ∀ i, ∃ (c : V) (hc : α i c = 2), (∀ x, α i x = 0 → B x c = 0) ∧
      ∃ g, ρ g = (Module.reflection hc).toLinearMap)
    (hfree : ∀ g x, (∀ i, α i x ≠ 0) → ρ g x = x → g = 1) (hx₀ : ∀ i, α i x₀ ≠ 0) {g : G}
    {x : V} (hx : x ∈ closedChamber α x₀) (hgx : ρ g x ∈ closedChamber α x₀) : ρ g x = x := by
  have hrefl' (i : ι) : ∃ (c : V) (hc : α i c = 2), ∃ g, ρ g = (Module.reflection hc).toLinearMap :=
    let ⟨c, hc, _, hg⟩ := hrefl i; ⟨c, hc, hg⟩
  set y := ρ g x
  -- The stabilizer of `y` contains the reflections in the walls through `y`.
  obtain ⟨h, hh, hS⟩ := ρ.exists_mem_forall_mem_le_mul hB (ρ.stabilizer y) {i | α i y = 0}
    (fun i hi ↦ by
      obtain ⟨c, hc, horth, s, hs⟩ := hrefl i
      refine ⟨c, hc, horth, s, ?_, hs⟩
      rw [mem_stabilizer, hs, LinearEquiv.coe_coe, Module.reflection_apply, Set.mem_ofPred.1 hi,
        zero_smul, sub_zero]) x₀ (ρ g x₀)
  rw [mem_stabilizer] at hh
  set v := ρ h (ρ g x₀)
  -- For small `t > 0`, the point `y + t v` lies in the closed chamber.
  obtain ⟨t, ht0, ht⟩ := exists_pos_add_smul_mem_closedChamber hgx hx₀ hS
  -- The element `h g` maps the regular point `x + t x₀` of the open chamber to `y + t v`.
  have himg : ρ (h * g) (x + t • x₀) = y + t • v := by
    rw [map_mul, mul_apply_eq_comp, map_add, map_smul, map_add, map_smul, hh]
  have hopen := add_smul_mem_openChamber hx hx₀ ht0
  have hyv : y + t • v ∈ openChamber α x₀ := by
    refine (mem_openChamber_iff_of_mem_closedChamber ht hx₀).2 (himg ▸
      ρ.apply_ne_zero_of_forall_apply_ne_zero hrefl' hfree _
        (fun _ ↦ apply_ne_zero_of_mem_openChamber hopen _))
  -- Hence `h g = 1`, so `g` fixes `y = ρ g x`, and `ρ g x = x`.
  have hhg := ρ.eq_one_of_apply_mem_openChamber hrefl' hfree hopen (himg ▸ hyv)
  rw [mul_eq_one_iff_eq_inv] at hhg
  rw [hhg] at hh
  have hgy : ρ g y = y := by
    have := congrArg (ρ g) hh
    rwa [self_inv_apply, eq_comm] at this
  calc ρ g x = ρ g⁻¹ (ρ g y) := by rw [inv_self_apply]
    _ = x := by rw [hgy]; exact inv_self_apply ρ g x

/-- **The closed chamber of a regular point is a strict fundamental domain.** Let `ρ` be a
representation of a finite group containing, for every `i`, the reflection in `ker α i` along a
coroot orthogonal to `ker α i` for a positive definite form `B`, and such that only the identity
fixes a regular point. If `x₀` lies on no hyperplane `ker α i`, every orbit meets the closed chamber
of `x₀` in exactly one point. -/
theorem existsUnique_mem_closedChamber_orbitRel [Finite G] [Finite ι]
    (hB : ∀ v, v ≠ 0 → 0 < B v v)
    (hrefl : ∀ i, ∃ (c : V) (hc : α i c = 2), (∀ x, α i x = 0 → B x c = 0) ∧
      ∃ g, ρ g = (Module.reflection hc).toLinearMap)
    (hfree : ∀ g x, (∀ i, α i x ≠ 0) → ρ g x = x → g = 1) (hx₀ : ∀ i, α i x₀ ≠ 0) (x : V) :
    ∃! y, y ∈ closedChamber α x₀ ∧ ρ.orbitRel y x := by
  obtain ⟨g, hg⟩ := ρ.exists_apply_mem_closedChamber hB hrefl x₀ x
  refine ⟨ρ g x, ⟨hg, ρ.orbitRel_apply.2 ⟨g, rfl⟩⟩, fun y ⟨hy, hxy⟩ ↦ ?_⟩
  obtain ⟨k, rfl⟩ := ρ.orbitRel_apply.1 hxy
  have h := ρ.apply_eq_self_of_apply_mem_closedChamber hB hrefl hfree hx₀ (g := g * k⁻¹) hy
    (by rwa [map_mul, mul_apply_eq_comp, inv_self_apply])
  rwa [map_mul, mul_apply_eq_comp, inv_self_apply, eq_comm] at h

/-! ### The closed chamber and the orbit space -/

variable [TopologicalSpace V]

/-- **The closed chamber of a regular point is homeomorphic to the orbit space.** Under the
hypotheses of `Representation.existsUnique_mem_closedChamber_orbitRel`, for a topology on `V` in
which every `ρ g` and every `α i` is continuous, the inclusion of the closed chamber of `x₀` into
`V` induces a homeomorphism onto the orbit space `V / G`. -/
noncomputable def closedChamberHomeomorph [Finite G] [Finite ι] (hB : ∀ v, v ≠ 0 → 0 < B v v)
    (hrefl : ∀ i, ∃ (c : V) (hc : α i c = 2), (∀ x, α i x = 0 → B x c = 0) ∧
      ∃ g, ρ g = (Module.reflection hc).toLinearMap)
    (hfree : ∀ g x, (∀ i, α i x ≠ 0) → ρ g x = x → g = 1) (hx₀ : ∀ i, α i x₀ ≠ 0)
    (hρ : ∀ g, Continuous (ρ g)) (hα : ∀ i, Continuous (α i)) :
    closedChamber α x₀ ≃ₜ Quotient ρ.orbitRel :=
  have hu := ρ.existsUnique_mem_closedChamber_orbitRel hB hrefl hfree hx₀
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (fun x : closedChamber α x₀ ↦ Quotient.mk ρ.orbitRel (x : V))
      ⟨fun x y hxy ↦ Subtype.ext <| (hu y).unique
          ⟨x.property, ρ.orbitRel_apply.2 (ρ.orbitRel_mk_eq_mk_iff.1 hxy)⟩
          ⟨y.property, ρ.orbitRel.iseqv.refl _⟩,
        fun q ↦ q.inductionOn fun x ↦ let ⟨y, ⟨hy, hxy⟩, _⟩ := hu x
          ⟨⟨y, hy⟩, ρ.orbitRel_mk_eq_mk_iff.2 (ρ.orbitRel_apply.1 hxy)⟩⟩)
    (continuous_quotient_mk'.comp continuous_subtypeVal)
    ((ρ.isClosedMap_orbitRel_mk_of_finite hρ).comp
      (isClosed_closedChamber hα).isClosedMap_subtypeVal)

/-- The homeomorphism `Representation.closedChamberHomeomorph` sends a point of the closed chamber
to its orbit. -/
@[simp]
theorem closedChamberHomeomorph_apply [Finite G] [Finite ι] (hB : ∀ v, v ≠ 0 → 0 < B v v)
    (hrefl : ∀ i, ∃ (c : V) (hc : α i c = 2), (∀ x, α i x = 0 → B x c = 0) ∧
      ∃ g, ρ g = (Module.reflection hc).toLinearMap)
    (hfree : ∀ g x, (∀ i, α i x ≠ 0) → ρ g x = x → g = 1) (hx₀ : ∀ i, α i x₀ ≠ 0)
    (hρ : ∀ g, Continuous (ρ g)) (hα : ∀ i, Continuous (α i)) (x : closedChamber α x₀) :
    ρ.closedChamberHomeomorph hB hrefl hfree hx₀ hρ hα x = Quotient.mk ρ.orbitRel (x : V) :=
  (rfl)

end Representation
