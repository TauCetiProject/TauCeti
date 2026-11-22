/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Associativity
public import TauCeti.Combinatorics.PlanarMatching.HalfDiagram.Glue
import all TauCeti.Combinatorics.PlanarMatching.Glue

/-!
# The through-strand factorization of Temperley–Lieb diagrams

A Temperley–Lieb diagram `f : n → m` with `f.through = m` has every top point on a through strand;
its strands look like a surjection from the bottom points onto the top points, and it is called
*string-surjective*. Dually, `g : m → p` with `g.through = m` has every bottom point on a through
strand and is called *string-injective*.

Composing with a string-surjective diagram on the bottom changes nothing at the top: if
`f.through = m` then `f ≫ g` has the top half-diagram of `g`, hence the same number of through
strands (`TauCeti.TLDiagram.topHalf_comp_val_of_through_eq_left`), and closes no new circle
(`TauCeti.TLDiagram.circles_comp_of_through_eq_left`). Dually, composing with a string-injective
diagram on top keeps the bottom half-diagram and closes no new circle
(`TauCeti.TLDiagram.bottomHalf_comp_val_of_through_eq_right`). In particular string-surjective
diagrams are closed under composition, and so are string-injective ones.

Every diagram `D : n → m` with `k = D.through` through strands factors as
`D = D.surjFactor ≫ D.injFactor` through `k` points: the string-surjective factor
`D.surjFactor : n → k` keeps the caps of `D` along the bottom and its closed circles, and the
string-injective factor `D.injFactor : k → m` keeps the cups of `D` along the top and has no
circles. A factorization through `k` points into a string-surjective and a string-injective
diagram is unique once the circles of the second factor are fixed
(`TauCeti.TLDiagram.comp_eq_comp_iff_of_through_eq`). For a composite `D₁ ≫ D₂`, the factorization
is computed from those of `D₁` and `D₂` by factoring the middle composite
`D₁.injFactor ≫ D₂.surjFactor` (`TauCeti.TLDiagram.comp_eq_comp_comp_middle`).

The factorization underlies the through-strand filtration of the diagram algebras, whose
layers are indexed by the number of through strands.

## Main definitions

* `TauCeti.TLDiagram.surjFactor D`, `TauCeti.TLDiagram.injFactor D`: the string-surjective and
  the string-injective factor of `D`.

## Main results

* `TauCeti.TLDiagram.topHalf_comp_val_of_through_eq_left`,
  `TauCeti.TLDiagram.bottomHalf_comp_val_of_through_eq_right`: composing with a string-surjective
  diagram below, or with a string-injective diagram above, keeps the far half-diagram.
* `TauCeti.TLDiagram.surjFactor_comp_injFactor`: the factorization `D.surjFactor ≫ D.injFactor = D`.
* `TauCeti.TLDiagram.comp_eq_comp_iff_of_through_eq`: uniqueness of the factorization.
* `TauCeti.TLDiagram.comp_eq_comp_comp_middle`: the factorization of a composite.

## Implementation notes

The partner of a top point in a composite is computed through the partner numbers of the
boundary points, using the private index arithmetic of
`TauCeti.Combinatorics.PlanarMatching.Glue`, which this file imports with `import all`. When every
top point of the lower diagram goes straight down, each strand entering the middle boundary from
above leaves it after one passage through the lower diagram, so gluing follows every strand for
at most one step and closes no circle.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
* D. Ridout and Y. Saint-Aubin, *Standard modules, induction and the structure of the
  Temperley–Lieb algebra*, arXiv:1204.4505.
-/

public section

namespace TauCeti

namespace PlanarMatching

variable {K n p : ℕ}

/-! ### Gluing along through strands -/

/-- The partner after gluing `j` middle pairs of the right outer point `n + 2 * j + t`, when every
left middle point is joined to a left outer point: a right outer or left outer partner stays, and
a right middle partner is followed once across the middle to the lower diagram. -/
private def rightOuterPartner (x : PlanarMatching K) (n j t : ℕ) : ℕ :=
  if n + 2 * j ≤ pv x (n + 2 * j + t) then pv x (n + 2 * j + t) - 2 * j
  else if n + j ≤ pv x (n + 2 * j + t) then pv x (2 * n + 2 * j - 1 - pv x (n + 2 * j + t))
  else pv x (n + 2 * j + t)

private theorem rightOuterPartner_cast {K' : ℕ} (h : K = K') (x : PlanarMatching K) (n j t : ℕ) :
    rightOuterPartner (cast h x) n j t = rightOuterPartner x n j t := by
  simp only [rightOuterPartner, pv_cast]

/-- Contracting the innermost middle pair does not move the partners of the other left middle
points, when these are joined to left outer points. -/
private theorem pv_contract_of_middle_lt {j : ℕ} (y : PlanarMatching (n + j + (j + p) + 2))
    (hy : ∀ s < j + 1, pv y (n + s) < n) {z : ℕ} (hz₁ : n ≤ z) (hz₂ : z < n + j) :
    pv (y.contract ⟨n + j, by omega⟩) z = pv y z := by
  have := hy (z - n) (by omega)
  rw [show n + (z - n) = z by omega] at this
  rw [pv_contract _ _ (by omega)]
  simp only [skipN, joinN, unskipN]
  split_ifs <;> omega

/-- Contracting the innermost middle pair does not change the eventual partners of the right outer
points, when every left middle point is joined to a left outer point. -/
private theorem rightOuterPartner_contract {j : ℕ} (y : PlanarMatching (n + j + (j + p) + 2))
    (hy : ∀ s < j + 1, pv y (n + s) < n) {t : ℕ} (ht : t < p) :
    rightOuterPartner (y.contract ⟨n + j, by omega⟩) n j t = rightOuterPartner y n (j + 1) t := by
  have hu := hy j (by omega)
  set v := pv y (n + 2 * (j + 1) + t) with hv
  have : v < n + j + (j + p) + 2 := pv_lt y (by omega)
  have hvv : pv y v = n + 2 * (j + 1) + t := pv_pv y (by omega)
  have hvmid : ¬ (n ≤ v ∧ v ≤ n + j) := by
    rintro ⟨h₁, h₂⟩
    have := hy (v - n) (by omega)
    rw [show n + (v - n) = v by omega] at this
    omega
  have hP : pv (y.contract ⟨n + j, by omega⟩) (n + 2 * j + t) =
      unskipN (n + j) (joinN y (n + j) v) := by
    rw [pv_contract _ _ (by omega), hv]
    congr 3
    simp only [skipN]
    split_ifs <;> omega
  simp only [rightOuterPartner]
  rw [hP, ← hv]
  by_cases hv₁ : v = n + j + 1
  · have hj : joinN y (n + j) v = pv y (n + j) := by
      simp only [joinN]
      split_ifs <;> omega
    -- The strand enters the middle at its innermost right point and leaves through `n + j`.
    obtain ⟨hu₁, hu₂, hu₃, hv₃, hv₄⟩ : pv y (n + j) < n + j ∧ ¬ n + 2 * j ≤ pv y (n + j) ∧
        ¬ n + j ≤ pv y (n + j) ∧ ¬ n + 2 * (j + 1) ≤ v ∧ n + (j + 1) ≤ v := by omega
    rw [hj, unskipN, ite_eq_left hu₁, ite_eq_right hu₂, ite_eq_right hu₃, ite_eq_right hv₃,
      ite_eq_left hv₄]
    congr 1
    omega
  · have hj : joinN y (n + j) v = v := by
      simp only [joinN]
      split_ifs <;> omega
    rw [hj]
    by_cases hv₂ : v < n
    · -- The strand already ends on the left outer boundary.
      simp only [unskipN]
      split_ifs <;> omega
    · rw [unskipN, ite_eq_right (show ¬ v < n + j by omega)]
      by_cases hv₃ : n + 2 * (j + 1) ≤ v
      · -- The strand ends on the right outer boundary.
        split_ifs <;> omega
      · -- The strand enters the middle at an outer right point and leaves through its mirror.
        obtain ⟨h₂, h₃, h₄⟩ : ¬ n + 2 * j ≤ v - 2 ∧ n + j ≤ v - 2 ∧ n + (j + 1) ≤ v := by omega
        rw [ite_eq_right h₂, ite_eq_left h₃, ite_eq_right hv₃, ite_eq_left h₄,
          pv_contract_of_middle_lt y hy (by omega) (by omega)]
        congr 1
        omega

/-- **Gluing along through strands.** If every left middle point of `x` is joined to a left outer
point, gluing across the middle closes no circle, and the partner of each right outer point is
`rightOuterPartner`. -/
private theorem glueMiddle_of_middle_lt :
    ∀ (j : ℕ) (x : PlanarMatching (n + j + (j + p))), (∀ s < j, pv x (n + s) < n) →
      glueMiddleCircles j x = 0 ∧
        ∀ t < p, pv (glueMiddle j x) (n + t) = rightOuterPartner x n j t
  | 0, x, _ => by
    refine ⟨rfl, fun t _ => ?_⟩
    rw [glueMiddle_zero, pv_cast]
    simp only [rightOuterPartner, mul_zero, add_zero, Nat.sub_zero]
    split_ifs <;> rfl
  | j + 1, x, h => by
    have hy : ∀ s < j + 1, pv (cast (k' := n + j + (j + p) + 2) (by omega) x) (n + s) < n :=
      fun s hs => (pv_cast _ x _).symm ▸ h s hs
    obtain ⟨ih₁, ih₂⟩ := glueMiddle_of_middle_lt j
      ((cast (k' := n + j + (j + p) + 2) (by omega) x).contract ⟨n + j, by omega⟩) fun s hs =>
      (pv_contract_of_middle_lt _ hy (z := n + s) (by omega) (by omega)).symm ▸ hy s (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · -- The innermost middle pair is not an arc, so its contraction closes no circle.
      have hu := hy j (by omega)
      rw [glueMiddleCircles_succ, ih₁, ite_eq_right fun he => ?_]
      rw [pv_of_lt _ (by omega), he] at hu
      simp only at hu
      omega
    · rw [glueMiddle_succ, ih₂ t ht, rightOuterPartner_contract _ hy ht, rightOuterPartner_cast]

end PlanarMatching

namespace TLDiagram

variable {n m p k : ℕ}

/-! ### Composing with string-surjective and string-injective diagrams -/

/-- In a diagram all of whose top points lie on through strands, each top point is joined to a
bottom point. -/
private theorem pv_lt_of_through_eq {f : TLDiagram n m} (hf : f.through = m) {s : ℕ}
    (hs : s < m) : PlanarMatching.pv f.matching (n + s) < n := by
  have h := (f.topHalf_apply_eq_self_iff ⟨m - 1 - s, by omega⟩).mp
    (by rw [HalfDiagram.val_eq_one_iff.mpr hf]; rfl)
  have he : (⟨n + m - 1 - (m - 1 - s), by omega⟩ : Fin (n + m)) = ⟨n + s, by omega⟩ :=
    Fin.ext (by simp only; omega)
  rw [PlanarMatching.pv_of_lt _ (by omega)]
  simpa only [he] using h

private theorem middle_lt_of_through_eq {f : TLDiagram n m} (hf : f.through = m)
    (g : TLDiagram m p) :
    ∀ s < m, PlanarMatching.pv (f.matching.append g.matching) (n + s) < n := fun s hs => by
  rw [PlanarMatching.pv_append_left _ _ (by omega)]
  exact pv_lt_of_through_eq hf hs

/-- Composing with a string-surjective diagram `f` below closes no new circle. -/
theorem circles_comp_of_through_eq_left {f : TLDiagram n m} (hf : f.through = m)
    (g : TLDiagram m p) : (f.comp g).circles = f.circles + g.circles := by
  rw [circles_comp, (PlanarMatching.glueMiddle_of_middle_lt m _
    (middle_lt_of_through_eq hf g)).1, add_zero]

/-- **Composing with a string-surjective diagram below keeps the top half-diagram**: if every top
point of `f` lies on a through strand, then `f ≫ g` has the cups of `g` along its top, and its
through strands end at the top endpoints of those of `g`. -/
theorem topHalf_comp_val_of_through_eq_left {f : TLDiagram n m} (hf : f.through = m)
    (g : TLDiagram m p) : (f.comp g).topHalf.val = g.topHalf.val := by
  ext j
  rw [topHalf_apply, topHalf_apply]
  set t := p - 1 - (j : ℕ)
  have hj := j.isLt
  -- The partner of the top point `j` in `f ≫ g` and in `g`, as numbers.
  have hA : ((f.comp g).matching.val.val ⟨n + p - 1 - j, by omega⟩ : ℕ) =
      PlanarMatching.rightOuterPartner (f.matching.append g.matching) n m t := by
    rw [← (PlanarMatching.glueMiddle_of_middle_lt m _ (middle_lt_of_through_eq hf g)).2 t
      (by omega), matching_comp, PlanarMatching.pv_of_lt _ (by omega)]
    congr 3
    omega
  have hG : (g.matching.val.val ⟨m + p - 1 - j, by omega⟩ : ℕ) =
      PlanarMatching.pv g.matching (m + t) := by
    rw [PlanarMatching.pv_of_lt _ (by omega)]
    congr 3
    omega
  have := PlanarMatching.pv_lt g.matching (q := m + t) (by omega)
  have hx : PlanarMatching.pv (f.matching.append g.matching) (n + 2 * m + t) =
      n + m + PlanarMatching.pv g.matching (m + t) := by
    rw [PlanarMatching.pv_append_right _ _ (by omega) (by omega)]
    congr 2
    omega
  -- A strand from `g` back down into `f` ends on the bottom of `f`.
  have hdown : PlanarMatching.pv g.matching (m + t) < m →
      PlanarMatching.pv (f.matching.append g.matching)
        (2 * n + 2 * m - 1 - (n + m + PlanarMatching.pv g.matching (m + t))) < n := fun h => by
    rw [show 2 * n + 2 * m - 1 - (n + m + PlanarMatching.pv g.matching (m + t)) =
      n + (m - 1 - PlanarMatching.pv g.matching (m + t)) by omega]
    exact middle_lt_of_through_eq hf g _ (by omega)
  simp only [PlanarMatching.rightOuterPartner, hx] at hA
  -- Either the strand from `j` stays in `g` and ends on its top, or it ends on the bottom of `f`.
  have key : (m ≤ PlanarMatching.pv g.matching (m + t) ∧
        ((f.comp g).matching.val.val ⟨n + p - 1 - j, by omega⟩ : ℕ) =
          n + PlanarMatching.pv g.matching (m + t) - m) ∨
      (PlanarMatching.pv g.matching (m + t) < m ∧
        ((f.comp g).matching.val.val ⟨n + p - 1 - j, by omega⟩ : ℕ) < n) := by
    rw [hA]
    by_cases hw' : m ≤ PlanarMatching.pv g.matching (m + t)
    · refine Or.inl ⟨hw', ?_⟩
      split_ifs <;> omega
    · refine Or.inr ⟨by omega, ?_⟩
      split_ifs with h₁ h₂
      · omega
      · exact hdown (by omega)
      · omega
  split_ifs <;> simp only <;> omega

/-- Composing with a string-surjective diagram below keeps the number of through strands. -/
theorem through_comp_of_through_eq_left {f : TLDiagram n m} (hf : f.through = m)
    (g : TLDiagram m p) : (f.comp g).through = g.through :=
  through_eq_of_topHalf_val_eq (topHalf_comp_val_of_through_eq_left hf g)

/-- Composing with a string-injective diagram `g` above closes no new circle. -/
theorem circles_comp_of_through_eq_right (f : TLDiagram n m) {g : TLDiagram m p}
    (hg : g.through = m) : (f.comp g).circles = f.circles + g.circles := by
  have h := circles_comp_of_through_eq_left (f := verticalReflect m p g)
    (by rw [through_verticalReflect, hg]) (verticalReflect n m f)
  rw [← verticalReflect_comp, circles_verticalReflect, circles_verticalReflect,
    circles_verticalReflect] at h
  omega

/-- **Composing with a string-injective diagram above keeps the bottom half-diagram**: if every
bottom point of `g` lies on a through strand, then `f ≫ g` has the caps of `f` along its bottom,
and its through strands start at the bottom endpoints of those of `f`. -/
theorem bottomHalf_comp_val_of_through_eq_right (f : TLDiagram n m) {g : TLDiagram m p}
    (hg : g.through = m) : (f.comp g).bottomHalf.val = f.bottomHalf.val := by
  have h := topHalf_comp_val_of_through_eq_left (f := verticalReflect m p g)
    (by rw [through_verticalReflect, hg]) (verticalReflect n m f)
  rwa [← verticalReflect_comp, topHalf_verticalReflect_val, topHalf_verticalReflect_val] at h

/-- Composing with a string-injective diagram above keeps the number of through strands. -/
theorem through_comp_of_through_eq_right (f : TLDiagram n m) {g : TLDiagram m p}
    (hg : g.through = m) : (f.comp g).through = f.through :=
  through_eq_of_bottomHalf_val_eq (bottomHalf_comp_val_of_through_eq_right f hg)

/-! ### The factorization -/

/-- The **string-surjective factor** of a diagram `D : n → m`: the diagram `n → D.through` with the
caps of `D` along its bottom, each through strand of `D` running straight up to the top, and the
closed circles of `D`. -/
def surjFactor (D : TLDiagram n m) : TLDiagram n D.through :=
  ⟨D.bottomHalf.glue (HalfDiagram.id D.through), D.circles⟩

/-- The **string-injective factor** of a diagram `D : n → m`: the diagram `D.through → m` with each
bottom point running up a through strand of `D`, the cups of `D` along its top, and no closed
circle. -/
def injFactor (D : TLDiagram n m) : TLDiagram D.through m :=
  ⟨(HalfDiagram.id D.through).glue D.topHalf, 0⟩

/-- The matching of the string-surjective factor: the bottom half-diagram of `D` with each defect
joined straight up to the top. -/
@[simp]
theorem matching_surjFactor (D : TLDiagram n m) :
    D.surjFactor.matching = D.bottomHalf.glue (HalfDiagram.id D.through) := (rfl)

/-- The string-surjective factor carries the closed circles of `D`. -/
@[simp]
theorem circles_surjFactor (D : TLDiagram n m) : D.surjFactor.circles = D.circles := (rfl)

/-- The matching of the string-injective factor: each bottom point joined straight up to a defect
of the top half-diagram of `D`. -/
@[simp]
theorem matching_injFactor (D : TLDiagram n m) :
    D.injFactor.matching = (HalfDiagram.id D.through).glue D.topHalf := (rfl)

/-- The string-injective factor has no closed circle. -/
@[simp]
theorem circles_injFactor (D : TLDiagram n m) : D.injFactor.circles = 0 := (rfl)

/-- The string-surjective factor of `D` has the bottom half-diagram of `D`. -/
@[simp]
theorem bottomHalf_surjFactor_val (D : TLDiagram n m) :
    D.surjFactor.bottomHalf.val = D.bottomHalf.val :=
  HalfDiagram.bottomHalf_glue_val _ _

/-- The string-injective factor of `D` has the top half-diagram of `D`. -/
@[simp]
theorem topHalf_injFactor_val (D : TLDiagram n m) : D.injFactor.topHalf.val = D.topHalf.val :=
  HalfDiagram.topHalf_glue_val _ _

/-- Every top point of the string-surjective factor lies on a through strand: its top half-diagram
has no arc. -/
@[simp]
theorem topHalf_surjFactor_val (D : TLDiagram n m) : D.surjFactor.topHalf.val = 1 :=
  (HalfDiagram.topHalf_glue_val _ _).trans (HalfDiagram.id_val _)

/-- Every bottom point of the string-injective factor lies on a through strand: its bottom
half-diagram has no arc. -/
@[simp]
theorem bottomHalf_injFactor_val (D : TLDiagram n m) : D.injFactor.bottomHalf.val = 1 :=
  (HalfDiagram.bottomHalf_glue_val _ _).trans (HalfDiagram.id_val _)

/-- The string-surjective factor of `D` is string-surjective: all of its top points lie on through
strands. -/
@[simp]
theorem through_surjFactor (D : TLDiagram n m) : D.surjFactor.through = D.through :=
  HalfDiagram.through_glue _ _

/-- The string-injective factor of `D` is string-injective: all of its bottom points lie on through
strands. -/
@[simp]
theorem through_injFactor (D : TLDiagram n m) : D.injFactor.through = D.through :=
  HalfDiagram.through_glue _ _

/-- **The through-strand factorization**: every diagram is its string-surjective factor followed
by its string-injective factor. -/
@[simp]
theorem surjFactor_comp_injFactor (D : TLDiagram n m) : D.surjFactor.comp D.injFactor = D := by
  apply ext_halves
  · rw [bottomHalf_comp_val_of_through_eq_right _ D.through_injFactor, bottomHalf_surjFactor_val]
  · rw [topHalf_comp_val_of_through_eq_left D.through_surjFactor, topHalf_injFactor_val]
  · rw [circles_comp_of_through_eq_left D.through_surjFactor, circles_surjFactor,
      circles_injFactor, add_zero]

/-- A string-surjective diagram followed by a string-injective one through `k` points has exactly
`k` through strands. -/
theorem through_comp_of_through_eq {f : TLDiagram n k} {g : TLDiagram k m} (hf : f.through = k)
    (hg : g.through = k) : (f.comp g).through = k :=
  (through_comp_of_through_eq_right f hg).trans hf

/-- **Uniqueness of the through-strand factorization**: two factorizations through `k` points into
a string-surjective and a string-injective diagram, whose string-injective factors carry the same
number of circles, agree. -/
theorem comp_eq_comp_iff_of_through_eq {f f' : TLDiagram n k} {g g' : TLDiagram k m}
    (hf : f.through = k) (hf' : f'.through = k) (hg : g.through = k) (hg' : g'.through = k)
    (hc : g.circles = g'.circles) : f.comp g = f'.comp g' ↔ f = f' ∧ g = g' := by
  refine ⟨fun h => ⟨ext_halves ?_ ?_ ?_, ext_halves ?_ ?_ hc⟩, fun h => h.1 ▸ h.2 ▸ rfl⟩
  · rw [← bottomHalf_comp_val_of_through_eq_right f hg, h,
      bottomHalf_comp_val_of_through_eq_right f' hg']
  · rw [HalfDiagram.val_eq_one_iff.mpr hf, HalfDiagram.val_eq_one_iff.mpr hf']
  · have := congrArg circles h
    rw [circles_comp_of_through_eq_left hf, circles_comp_of_through_eq_left hf'] at this
    omega
  · rw [HalfDiagram.val_eq_one_iff.mpr hg, HalfDiagram.val_eq_one_iff.mpr hg']
  · rw [← topHalf_comp_val_of_through_eq_left hf g, h, topHalf_comp_val_of_through_eq_left hf' g']

/-- **The factorization of a composite**: `D₁ ≫ D₂` is the string-surjective factor of `D₁` and that
of the middle composite `D₁.injFactor ≫ D₂.surjFactor`, followed by the string-injective factor of
the middle composite and that of `D₂`. The two factors are string-surjective and string-injective
(`TauCeti.TLDiagram.through_surjFactor_comp_surjFactor`,
`TauCeti.TLDiagram.through_injFactor_comp_injFactor`), and the second has no closed circle. -/
theorem comp_eq_comp_comp_middle (D₁ : TLDiagram n m) (D₂ : TLDiagram m p) :
    D₁.comp D₂ = (D₁.surjFactor.comp (D₁.injFactor.comp D₂.surjFactor).surjFactor).comp
      ((D₁.injFactor.comp D₂.surjFactor).injFactor.comp D₂.injFactor) := by
  conv_lhs => rw [← D₁.surjFactor_comp_injFactor, ← D₂.surjFactor_comp_injFactor]
  simp only [comp_assoc]
  congr 1
  rw [← comp_assoc D₁.injFactor, ← comp_assoc (D₁.injFactor.comp D₂.surjFactor).surjFactor,
    surjFactor_comp_injFactor]

/-- The first factor in the factorization of a composite is string-surjective. -/
theorem through_surjFactor_comp_surjFactor (D₁ : TLDiagram n m) (D₂ : TLDiagram m p) :
    (D₁.surjFactor.comp (D₁.injFactor.comp D₂.surjFactor).surjFactor).through =
      (D₁.injFactor.comp D₂.surjFactor).through := by
  rw [through_comp_of_through_eq_left D₁.through_surjFactor, through_surjFactor]

/-- The second factor in the factorization of a composite is string-injective. -/
theorem through_injFactor_comp_injFactor (D₁ : TLDiagram n m) (D₂ : TLDiagram m p) :
    ((D₁.injFactor.comp D₂.surjFactor).injFactor.comp D₂.injFactor).through =
      (D₁.injFactor.comp D₂.surjFactor).through := by
  rw [through_comp_of_through_eq_right _ D₂.through_injFactor, through_injFactor]

/-- The second factor in the factorization of a composite has no closed circle. -/
theorem circles_injFactor_comp_injFactor (D₁ : TLDiagram n m) (D₂ : TLDiagram m p) :
    ((D₁.injFactor.comp D₂.surjFactor).injFactor.comp D₂.injFactor).circles = 0 := by
  rw [circles_comp_of_through_eq_right _ D₂.through_injFactor, circles_injFactor,
    circles_injFactor]

/-- A composite has as many through strands as the composite of the string-injective factor of the
first diagram with the string-surjective factor of the second. -/
theorem through_comp (D₁ : TLDiagram n m) (D₂ : TLDiagram m p) :
    (D₁.comp D₂).through = (D₁.injFactor.comp D₂.surjFactor).through := by
  rw [comp_eq_comp_comp_middle, through_comp_of_through_eq (through_surjFactor_comp_surjFactor _ _)
    (through_injFactor_comp_injFactor _ _)]

end TLDiagram

/-- The generator `e₁ = cap ≫ cup : 2 → 2` has no through strand. -/
example : (TLDiagram.cap.comp TLDiagram.cup).through = 0 :=
  TLDiagram.through_comp_of_through_eq (TLDiagram.through_zero_right _)
    (TLDiagram.through_zero_left _)

/-- The only factorization of `e₁` through the empty boundary whose upper factor has no closed
circle is the cap followed by the cup. -/
example (f : TLDiagram 2 0) (g : TLDiagram 0 2) (hg : g.circles = 0)
    (h : f.comp g = TLDiagram.cap.comp TLDiagram.cup) : f = TLDiagram.cap ∧ g = TLDiagram.cup :=
  (TLDiagram.comp_eq_comp_iff_of_through_eq (TLDiagram.through_zero_right f)
    (TLDiagram.through_zero_right _) (TLDiagram.through_zero_left g)
    (TLDiagram.through_zero_left _) (hg.trans TLDiagram.circles_cup.symm)).mp h

/-- String-surjective diagrams compose: below a diagram whose top points all go through, a second
such diagram keeps all its top points on through strands. -/
example {n m p : ℕ} (f : TLDiagram n m) (g : TLDiagram m p) (hf : f.through = m)
    (hg : g.through = p) : (f.comp g).through = p :=
  (TLDiagram.through_comp_of_through_eq_left hf g).trans hg

end TauCeti
