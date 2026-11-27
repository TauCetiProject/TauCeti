/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.ExceptionalImage
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic

/-!
# Examples: curve classes and counts on `ℂP²` and on the blown-up K3 surface

Taubes's count of embedded pseudoholomorphic curves in a closed symplectic four-manifold `X` is
governed by the intersection form `B` on `H₂(X; ℤ)` and the canonical class `κ`. The virtual
dimension of a class `e` is the integer `d(e) = e · e - κ · e`, the index of a curve in that
class; a class is *good* if it pairs to at least `-1` with every embedded pseudoholomorphic sphere
of square `-1`. This file tests the intersection algebra of `TauCeti.IsRegularSimpleCurve`,
`TauCeti.IsGoodCycle`, `TauCeti.IsCanonicalCycle`, `TauCeti.IsGoodClass` and the counts
`TauCeti.configurationCount` and `TauCeti.pointConfigurationCount` on the standard examples,
and shows how each competing convention fails.

**The projective plane.** The intersection form of `ℂP²` is `x · y = x y` on `H₂ = ℤ`, generated
by the class `H` of a line (`LinearMap.mul ℤ ℤ`), and `κ = -3 H`.

* `κ` is characteristic for the intersection form (`isCharacteristic_mul_neg_three`), so every
  virtual dimension is even (`two_dvd_sq_add_three_mul`): `d(j H) = j² + 3 j`
  (`mul_apply_self_sub_apply_neg_three`), with `d / 2 = 0, 2, 5, 9` for `j = 0, 1, 2, 3`
  (`mul_apply_self_sub_apply_neg_three_eq`), the numbers of points through which curves of
  degree `j` are counted.
* A regular simple curve in the class of a line is an embedded sphere
  (`isRegularSimpleCurve_one_iff`): the adjunction formula `H · H + κ · H = -2` forces genus and
  singularity number zero. Its index is `4`, two point constraints, while the sign convention
  `H · H + κ · H` would give `-2`.
* With candidate curves all in the class of a line, the weighted count through some points in
  the class `H` is the weight of the unique candidate through all of them
  (`pointConfigurationCount_one_eq`). Through two ordered points, with the line counted with
  sign `+1`, the count is `1`, the weight of the single line, so it is not divided by the `2!`
  orderings of the points. It also does not depend on the order of the points
  (`TauCeti.pointConfigurationCount_map_equiv`).

**The blown-up K3 surface.** A K3 surface has `κ = 0`; its blowup at a point has `κ = E` for the
exceptional class `E`, of square `-1`. The statements below need only these two numbers, so they
are made for any intersection lattice with a class `E` of square `-1` and `κ = E`.

* The label `e = 2 E` has `e · e = -4` and `κ · e = -2`, so `d(2 E) = -2`
  (`apply_two_smul_self_sub_apply_two_smul`): it has negative dimension. Clamping this dimension
  to `ℕ` with `Int.toNat`, as for a natural-number dimension, would return `0`.
* The class `2 E` is not good, since `2 E · E = -2 < -1` (`apply_two_smul_lt_neg_one`), and both
  vanishing theorems apply to it: the count in class `2 E` vanishes because the class is bad
  (`TauCeti.configurationCount_eq_zero_of_apply_lt_neg_one`) and because its dimension is
  negative (`TauCeti.configurationCount_eq_zero_of_apply_self_sub_apply_canonical_neg`).
* The exceptional sphere, with multiplicity one, is a canonical cycle
  (`isCanonicalCycle_const_one`); with multiplicity two it is not, for any `κ`, since it would
  force `κ = 2 E` and so `κ · E = -2` rather than `-1` (`not_isCanonicalCycle_const_two`).

**Exceptional spheres and tori.** By adjunction, a regular simple curve of negative square has
square `-1`, pairs to `-1` with `κ` and has index `0`, and a regular simple torus of square zero
is embedded and orthogonal to `κ`
(`TauCeti.IsRegularSimpleCurve.apply_canonical_eq_zero_of_genus_eq_one`), so of index `0`. So if
every exceptional image satisfies the adjunction formula for a sphere, the canonical class is good
(`TauCeti.isGoodClass_canonical`), while it is negative on every such exceptional image: the
condition `0 ≤ e · S` in place of `-1 ≤ e · S` would make `κ` bad for any `J` with an exceptional
image.

**Multiple covers.** The virtual dimension of `m C` is `m d(C) + m (m - 1) C · C`. On a K3
surface (`κ = 0`) a square-zero torus `T` therefore gives `d(2 T) = 0`, and `2 T` is a good cycle
through no points (`isGoodCycle_const_two`). For a class `C` of nonzero square, the
single-component cycle `2 C` is not a good cycle (`not_isGoodCycle_const_two`). For a symmetric
intersection form, every component of multiplicity above one has square zero
(`TauCeti.IsGoodCycle.apply_self_eq_zero_of_one_lt_mult`).

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* D. McDuff, *Lectures on Gromov invariants for symplectic 4-manifolds*, arXiv:dg-ga/9606005.
-/

public section

open LinearMap (BilinForm)
open scoped Manifold ContDiff

namespace TauCeti.Examples.CurveClasses

/-! ### The projective plane -/

section ProjectivePlane

/-- The canonical class `κ = -3 H` of `ℂP²` is characteristic for its intersection form
`x · y = x y` on `H₂(ℂP²; ℤ) = ℤ`. -/
theorem isCharacteristic_mul_neg_three : BilinForm.IsCharacteristic (LinearMap.mul ℤ ℤ) (-3) := by
  have h : (-3 : ℤ) = -(1 + (2 : ℤ) • 1) := by norm_num
  rw [h, BilinForm.isCharacteristic_neg_iff, BilinForm.isCharacteristic_add_two_smul_iff]
  exact BilinForm.isCharacteristic_mul_one fun x ↦
    by simpa [sq, mul_sub] using (Int.even_mul_pred_self x).two_dvd

/-- The virtual dimension `d(j H) = (j H) · (j H) - κ · (j H)` of a class of `ℂP²` is
`j² + 3 j`. -/
theorem mul_apply_self_sub_apply_neg_three (j : ℤ) :
    LinearMap.mul ℤ ℤ j j - LinearMap.mul ℤ ℤ (-3) j = j ^ 2 + 3 * j := by
  simp only [LinearMap.mul_apply']
  ring

/-- Every virtual dimension of `ℂP²` is even, because `κ` is characteristic. -/
theorem two_dvd_sq_add_three_mul (j : ℤ) : 2 ∣ j ^ 2 + 3 * j := by
  rw [← mul_apply_self_sub_apply_neg_three]
  simpa using (BilinForm.isCharacteristic_iff.1 isCharacteristic_mul_neg_three j).neg_right

/-- The classes of degree `j = 0, 1, 2, 3` of `ℂP²` have virtual dimension `2 k` for
`k = 0, 2, 5, 9`: the empty curve, the line through two points, the conic through five points
and the cubic through nine points. -/
theorem mul_apply_self_sub_apply_neg_three_eq :
    LinearMap.mul ℤ ℤ 0 0 - LinearMap.mul ℤ ℤ (-3) 0 = 2 * 0 ∧
      LinearMap.mul ℤ ℤ 1 1 - LinearMap.mul ℤ ℤ (-3) 1 = 2 * 2 ∧
      LinearMap.mul ℤ ℤ 2 2 - LinearMap.mul ℤ ℤ (-3) 2 = 2 * 5 ∧
      LinearMap.mul ℤ ℤ 3 3 - LinearMap.mul ℤ ℤ (-3) 3 = 2 * 9 := by
  simp only [mul_apply_self_sub_apply_neg_three]
  norm_num

/-- **A simple curve in the class of a line is an embedded sphere.** The numerical conditions of
a regular simple curve of genus `g` and singularity number `δ` in the class `H` of `ℂP²` hold
exactly for `g = δ = 0`. -/
theorem isRegularSimpleCurve_one_iff {g δ : ℕ} :
    IsRegularSimpleCurve (LinearMap.mul ℤ ℤ) (-3) 1 g δ ↔ g = 0 ∧ δ = 0 := by
  constructor
  · intro h
    have := h.adjunction
    simp only [LinearMap.mul_apply'] at this
    omega
  · rintro ⟨rfl, rfl⟩
    exact ⟨by norm_num, by norm_num⟩

/-- The index `2 g - 2 - 2 κ · H` of a simple curve in the class of a line of `ℂP²` is `4`:
lines are counted through two points. -/
example {g δ : ℕ} (h : IsRegularSimpleCurve (LinearMap.mul ℤ ℤ) (-3) 1 g δ) :
    2 * (g : ℤ) - 2 - 2 * LinearMap.mul ℤ ℤ (-3) 1 = 4 := by
  obtain ⟨rfl, -⟩ := isRegularSimpleCurve_one_iff.1 h
  norm_num

/-- The opposite sign convention `H · H + κ · H` for the index of a line would give `-2`. -/
example : LinearMap.mul ℤ ℤ 1 1 + LinearMap.mul ℤ ℤ (-3) 1 = -2 := by
  norm_num

variable {ι P R : Type*} [CommSemiring R] {r : ι → ι → Prop} {pts : ι → Finset P}
  {w : ι → ℕ → R} {s : Set ι} {c₀ : ι}

/-- If every candidate lies in the class of a line, the configurations in the class `H` covering
the points are the single candidates, with multiplicity one, passing through all the points. -/
theorem pointConfigurations_one :
    pointConfigurations r (fun _ ↦ (1 : ℤ)) pts s 1 =
      (fun c ↦ Finsupp.single c 1) '' {c ∈ s | ∀ p, p ∈ pts c} := by
  ext l
  simp only [mem_pointConfigurations, mem_compatibleConfigurations, Set.mem_image,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hs, -, hl⟩, hcov⟩
    -- The class of `l` is its total multiplicity, so `l` is a single candidate.
    have hsum : (l.sum fun _ n ↦ n) = 1 := by
      have : ((l.sum fun _ n ↦ n : ℕ) : ℤ) = 1 := by
        rw [← hl]
        simp [Finsupp.linearCombination_apply, Finsupp.sum]
      exact_mod_cast this
    obtain ⟨c, rfl⟩ := (Finsupp.sum_eq_one_iff l).1 hsum
    refine ⟨c, ⟨hs (by simp), fun p ↦ ?_⟩, rfl⟩
    obtain ⟨d, hd, hp⟩ := hcov p
    rw [Finsupp.support_single c one_ne_zero, Finset.mem_singleton] at hd
    exact hd ▸ hp
  · rintro ⟨c, ⟨hc, hcov⟩, rfl⟩
    exact ⟨⟨by simpa using hc, by simp, by simp⟩, fun p ↦ ⟨c, by simp, hcov p⟩⟩

/-- **The count of lines through points.** If every candidate lies in the class `H` of a line of
`ℂP²` and `c₀` is the only candidate passing through all the points, then the weighted count
through the points in the class `H` is the weight `w c₀ 1` of `c₀`, with multiplicity one. -/
theorem pointConfigurationCount_one_eq (hc₀ : c₀ ∈ s)
    (huniq : ∀ c ∈ s, (∀ p, p ∈ pts c) → c = c₀) (hcov : ∀ p, p ∈ pts c₀) :
    pointConfigurationCount r (fun _ ↦ (1 : ℤ)) pts w s 1 = w c₀ 1 := by
  have h : {c ∈ s | ∀ p, p ∈ pts c} = {c₀} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨⟨hc₀, hcov⟩, fun c hc ↦ huniq c hc.1 hc.2⟩
  rw [pointConfigurationCount_def, pointConfigurations_one, h]
  simp [Finsupp.prod]

/-- **One line through two points.** With candidates in the class `H` of `ℂP²`, only one of which
passes through two given points, and that line counted with sign `+1`, the count through the two
points in the class `H` is `1`, the weight of the single line: the count is not divided by the
`2!` orderings of the points. -/
example {pts : ι → Finset (Fin 2)} (hc₀ : c₀ ∈ s)
    (huniq : ∀ c ∈ s, (∀ p, p ∈ pts c) → c = c₀) (hcov : ∀ p, p ∈ pts c₀) (hw : w c₀ 1 = 1) :
    pointConfigurationCount r (fun _ ↦ (1 : ℤ)) pts w s 1 = 1 :=
  (pointConfigurationCount_one_eq hc₀ huniq hcov).trans hw

/-- The count through two points does not depend on their order: exchanging the two points
leaves it unchanged. -/
example {pts : ι → Finset (Fin 2)} :
    pointConfigurationCount r (fun _ ↦ (1 : ℤ)) (fun c ↦ (pts c).map (Equiv.swap 0 1).toEmbedding)
      w s 1 = pointConfigurationCount r (fun _ ↦ (1 : ℤ)) pts w s 1 :=
  pointConfigurationCount_map_equiv _

end ProjectivePlane

/-! ### Exceptional spheres and square-zero tori -/

section Adjunction

variable {H : Type*} [AddCommGroup H] {B : BilinForm ℤ H} {κ c : H} {g δ : ℕ}

/-- An exceptional sphere, a regular simple curve of negative square, has square `-1`, pairs to
`-1` with the canonical class, and has index `c · c - κ · c = 0`. -/
example (h : IsRegularSimpleCurve B κ c g δ) (hc : B c c < 0) :
    B c c = -1 ∧ B κ c = -1 ∧ B c c - B κ c = 0 := by
  have h₁ := h.apply_self_eq_neg_one_of_apply_self_neg hc
  have h₂ := h.apply_canonical_eq_neg_one_of_apply_self_neg hc
  omega

/-- A regular simple torus of square zero is orthogonal to the canonical class, embedded, and
has index `c · c - κ · c = 0`. -/
example (h : IsRegularSimpleCurve B κ c 1 δ) (hc : B c c = 0) :
    B κ c = 0 ∧ δ = 0 ∧ B c c - B κ c = 0 := by
  have hκ := h.apply_canonical_eq_zero_of_genus_eq_one hc
  have hδ := h.singularity_eq_zero_of_apply_canonical_eq_apply_self (hκ.trans hc.symm)
  omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  {I : ModelWithCorners ℝ E M} {X : Type} [TopologicalSpace X] [ChartedSpace M X]
  [IsManifold I ∞ X] {J : SmoothAlmostComplexStructure I X} {B : IntersectionForm X}
  {κ : secondHomology X} {S : Set X}

/-- The canonical class is negative on an exceptional image satisfying the adjunction formula
for a sphere. So, for any `J` with such an exceptional image, `κ` would not be good for the
condition `0 ≤ e · [S]`, although it is good if every exceptional image satisfies the sphere
adjunction formula (`TauCeti.isGoodClass_canonical`). -/
example (hS : S ∈ exceptionalImages J B)
    (hadj : B (embeddedCurveClass J S) (embeddedCurveClass J S) + B κ (embeddedCurveClass J S) =
      -2) :
    ¬0 ≤ B κ (embeddedCurveClass J S) := by
  rw [apply_canonical_eq_neg_one_of_mem_exceptionalImages hS hadj]
  norm_num

end Adjunction

/-! ### The blown-up K3 surface -/

section Blowup

variable {H : Type*} [AddCommGroup H] {B : BilinForm ℤ H} {E : H}

/-- With `κ = E` of square `-1`, the label `e = 2 E` has `e · e = -4`, `κ · e = -2` and virtual
dimension `d(2 E) = -2`. -/
theorem apply_two_smul_self_sub_apply_two_smul (hE : B E E = -1) :
    B ((2 : ℤ) • E) ((2 : ℤ) • E) = -4 ∧ B E ((2 : ℤ) • E) = -2 ∧
      B ((2 : ℤ) • E) ((2 : ℤ) • E) - B E ((2 : ℤ) • E) = -2 := by
  simp only [map_zsmul, LinearMap.smul_apply, hE]
  norm_num

/-- Clamping the dimension to `ℕ` with `Int.toNat` would give the label `2 E` dimension `0`
instead of `-2`. -/
example (hE : B E E = -1) :
    (B ((2 : ℤ) • E) ((2 : ℤ) • E) - B E ((2 : ℤ) • E)).toNat = 0 := by
  rw [(apply_two_smul_self_sub_apply_two_smul hE).2.2]
  decide

/-- The class `2 E` is not good: it pairs to `-2 < -1` with the exceptional class. -/
theorem apply_two_smul_lt_neg_one (hE : B E E = -1) : B ((2 : ℤ) • E) E < -1 := by
  simp only [map_zsmul, LinearMap.smul_apply, hE]
  norm_num

variable {ι R : Type*} [CommSemiring R] {r : ι → ι → Prop} {cls : ι → H} {w : ι → ℕ → R}
  {s : Set ι}

/-- **The count vanishes in the bad class `2 E`.** If the exceptional sphere `S` of class `E` is
counted with multiplicity one only and every other candidate meets it nonnegatively, the count in
class `2 E` vanishes. -/
example {S : ι} (hSE : cls S = E) (hE : B E E = -1)
    (hpos : ∀ c ∈ s, c ≠ S → 0 ≤ B (cls c) (cls S)) (hw : ∀ k, 2 ≤ k → w S k = 0) :
    configurationCount r cls w s ((2 : ℤ) • E) = 0 :=
  configurationCount_eq_zero_of_apply_lt_neg_one hpos (by rw [hSE, hE]) hw
    (by rw [hSE]; exact apply_two_smul_lt_neg_one hE)

/-- **The count vanishes in the class `2 E` of negative dimension**, under the hypotheses of
`TauCeti.configurationCount_eq_zero_of_apply_self_sub_apply_canonical_neg` for `κ = E`. -/
example (hE : B E E = -1)
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hind : ∀ c ∈ s, 0 ≤ B (cls c) (cls c) - B E (cls c))
    (hmult : ∀ c ∈ s, ∀ k, 2 ≤ k → w c k ≠ 0 → 0 ≤ B (cls c) (cls c)) :
    configurationCount r cls w s ((2 : ℤ) • E) = 0 := by
  refine configurationCount_eq_zero_of_apply_self_sub_apply_canonical_neg hr hind hmult ?_
  rw [(apply_two_smul_self_sub_apply_two_smul hE).2.2]
  norm_num

/-- **The exceptional sphere is a canonical cycle.** With `κ = E` of square `-1`, the cycle
consisting of `E` with multiplicity one is canonical. -/
theorem isCanonicalCycle_const_one (hE : B E E = -1) :
    IsCanonicalCycle B E (fun _ : Unit ↦ E) (fun _ ↦ 1) where
  mult_pos _ := one_pos
  apply_nonneg_of_ne {i j} hij := absurd (Subsingleton.elim i j) hij
  apply_canonical_le_apply_self _ := le_rfl
  apply_self_eq_neg_one_of_apply_self_neg _ _ := hE
  apply_canonical_eq_neg_one_of_apply_self_neg _ _ := hE
  sum_eq := by simp

/-- **An exceptional sphere does not occur twice in a canonical cycle.** If `E` has square `-1`,
the cycle `2 E` is not canonical for any `κ`: it forces `κ = 2 E`, so `κ · E = -2`, while a
canonical cycle needs `κ · E = -1`. -/
theorem not_isCanonicalCycle_const_two {κ : H} (hE : B E E = -1) :
    ¬IsCanonicalCycle B κ (fun _ : Unit ↦ E) (fun _ ↦ 2) := by
  intro h
  have hκ := h.apply_canonical_eq_neg_one_of_apply_self_neg () (by rw [hE]; norm_num)
  have hsum := h.sum_eq
  simp only [Finset.univ_unique, Finset.sum_singleton] at hsum
  rw [← hsum, map_nsmul, LinearMap.smul_apply, hE] at hκ
  norm_num at hκ

end Blowup

/-! ### Multiple covers -/

section MultipleCover

variable {H : Type*} [AddCommGroup H] {B : BilinForm ℤ H} {κ C T : H}

/-- The virtual dimension of a multiple: `d(m C) = m d(C) + m (m - 1) C · C`. -/
example (m : ℕ) :
    B (m • C) (m • C) - B κ (m • C) = m * (B C C - B κ C) + m * (m - 1) * B C C := by
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  ring

/-- **A double square-zero torus on a K3 surface is a good cycle.** For `κ = 0` and a class `T`
of square zero, the cycle `2 T` through no points satisfies the conditions of
`TauCeti.IsGoodCycle`: its virtual dimension is `0`. -/
theorem isGoodCycle_const_two (hT : B T T = 0) :
    IsGoodCycle B 0 ((2 : ℕ) • T) (fun _ : Unit ↦ T) (fun _ ↦ 2) (fun _ ↦ 0)
      (fun _ ↦ (∅ : Finset Empty)) where
  mult_pos _ := two_pos
  apply_nonneg {i j} hij := absurd (Subsingleton.elim i j) hij
  two_mul_card_add_le _ := by simp [hT]
  neg_one_le_apply _ h := absurd h (by simp [hT])
  sum_eq := by simp
  exists_mem p := p.elim
  apply_self_sub_apply_canonical := by simp [hT]

/-- **Multiplicity two excludes nonzero square.** The cycle `2 C`, for a class `C` of nonzero
square, is not a good cycle: a good cycle has `e · C = C · C`, while here `e · C = 2 C · C`. -/
theorem not_isGoodCycle_const_two {P : Type*} [Fintype P] {e : H} {δ : Unit → ℕ}
    {pts : Unit → Finset P} (hC : B C C ≠ 0) :
    ¬IsGoodCycle B κ e (fun _ ↦ C) (fun _ ↦ 2) δ pts := fun h ↦ by
  have he := h.apply_eq_apply_self ()
  rw [← h.sum_eq] at he
  simp only [Finset.univ_unique, Finset.sum_singleton, two_nsmul, map_add,
    LinearMap.add_apply] at he
  omega

end MultipleCover

end TauCeti.Examples.CurveClasses
