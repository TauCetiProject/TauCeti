/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LambdaTree.Action

/-!
# Chiswell's `Λ`-tree construction from a Lyndon length function

Every isometric action of a group `G` on a `Λ`-tree `X` with a base point `x₀` determines a based
Lyndon length function `g ↦ d x₀ (g • x₀)` whose Gromov products lie in `Λ`, and the action is free
if and only if this length function is free (`TauCeti.LambdaMetric.IsTree.isFree_basedLength_iff`).
Chiswell's construction proves the converse: from a Lyndon length function `l : LyndonLength G Λ`
one builds a `Λ`-metric space `l.Chiswell` with an isometric `G`-action and a base point
`l.chiswellBase`, which is a `Λ`-tree with based length function `l` if and only if the Gromov
products of `l` lie in `Λ` (axiom (L4)).

Geometrically `l.Chiswell` glues together copies `{(g, s) | 0 ≤ s ≤ l g}` of the intervals
`[0, l g]` along their initial segments `[0, c(g, f)]`: two pairs `(g, s)` and `(f, t)` represent
the same point when `s = t ≤ c(g, f)`, and the distance between `(g, s)` and `(f, t)` is
`s + t - 2 min(s, t, c(g, f))`. Neither the carrier, the geodesic `Λ`-metric
(`TauCeti.LyndonLength.isGeodesic_chiswellMetric`), nor the isometric `G`-action requires axiom
(L4), because all comparisons with `c(g, f)` are stated for the doubled Gromov product
`l g + l f - l (g⁻¹ * f) ∈ Λ`. Axiom (L4) is the exact condition under which the branch point
`(g, c(g, f))` exists in `l.Chiswell`, making `l.chiswellMetric` a `Λ`-tree.

Moreover, for any isometric `G`-action on a `Λ`-tree `X` with a base point `x₀` whose based length
function is `l`, there is a unique `G`-equivariant isometric embedding `l.chiswellEmbed` of
`l.Chiswell` into `X` sending `l.chiswellBase` to `x₀`, with range the union of segments
`⋃ g : G, [x₀, g • x₀]`. Combining Chiswell's construction with `isFree_basedLength_iff` shows
that a group has a free `Λ`-valued Lyndon length function if and only if it acts freely on a
`Λ`-tree (`TauCeti.LyndonLength.exists_isFree_iff`).

## Main definitions

* `TauCeti.LyndonLength.Chiswell`: the quotient of `{(g, s) : G × Λ | 0 ≤ s ≤ l g}` by the
  equivalence relation `(g, s) ≈ (f, t) ↔ s = t ∧ 2 • s ≤ l g + l f - l (g⁻¹ * f)`.
* `TauCeti.LyndonLength.chiswellMk`, `TauCeti.LyndonLength.chiswellLift`: constructor and quotient
  eliminator for `l.Chiswell`.
* `TauCeti.LyndonLength.chiswellBase`: the base point `(1, 0)` of `l.Chiswell`.
* `TauCeti.LyndonLength.chiswellMetric`: the geodesic `Λ`-metric on `l.Chiswell`.
* `TauCeti.LyndonLength.instMulActionChiswell`: the isometric `G`-action on `l.Chiswell`.
* `TauCeti.LyndonLength.chiswellEmbed`: the `G`-equivariant isometric embedding of `l.Chiswell`
  onto `⋃ g : G, [x₀, g • x₀]` in any based `G`-`Λ`-tree realising `l`.

## Main results

* `TauCeti.LyndonLength.isGeodesic_chiswellMetric`: `l.chiswellMetric` is geodesic.
* `TauCeti.LyndonLength.isIsometricAction_chiswellMetric`: `G` acts on `l.Chiswell` by isometries.
* `TauCeti.LyndonLength.isTree_chiswellMetric`, `TauCeti.LyndonLength.isTree_chiswellMetric_iff`:
  `l.chiswellMetric` is a `Λ`-tree if and only if the Gromov products of `l` lie in `Λ`.
* `TauCeti.LyndonLength.basedLength_chiswellBase`: at `l.chiswellBase`, the based length function of
  `l.Chiswell` is `l`.
* `TauCeti.LyndonLength.chiswellEmbed_unique`: `chiswellEmbed` is the unique `G`-equivariant
  isometric map `l.Chiswell → X` sending `l.chiswellBase` to `x₀`.
* `TauCeti.LyndonLength.isFreeAction_chiswell_iff`: when `l` satisfies (L4), the action of `G` on
  `l.Chiswell` is free if and only if `l` is free.
* `TauCeti.LyndonLength.exists_basedLength_eq_iff`: `l` is the based length function of an isometric
  action on a `Λ`-tree if and only if its Gromov products lie in `Λ`.
* `TauCeti.LyndonLength.exists_isFree_iff`: `G` has a free `Λ`-valued Lyndon length function if and
  only if `G` acts freely on a `Λ`-tree.

## References

* I. Chiswell, *Introduction to Λ-trees*, World Scientific, 2001, §§2.2, 2.4, and 3.1.
* R. C. Lyndon, *Length functions in groups*, Math. Scand. 12 (1963), 209–234.
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Groups with free regular length
  functions in `ℤⁿ`*, Trans. Amer. Math. Soc. 364 (2012), §2.1, Theorem 1.
* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-Archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), §5.
-/

public section

namespace TauCeti.LyndonLength

open Set

universe u v

variable {G : Type u} {Λ : Type v} [Group G] [AddCommGroup Λ] [LinearOrder Λ]
  [IsOrderedAddMonoid Λ]

/-! ### Doubled Gromov products -/

section DoubleGromov

variable (l : LyndonLength G Λ)

/-- Twice the Gromov product `c(g, f)`, as an element of `Λ`. -/
private def doubleGromov (g f : G) : Λ :=
  l g + l f - l (g⁻¹ * f)

private theorem doubleGromov_comm (g f : G) : doubleGromov l g f = doubleGromov l f g :=
  l.gromovProduct_eq_gromovProduct_iff.1 (l.gromovProduct_comm g f)

private theorem doubleGromov_self (g : G) : doubleGromov l g g = 2 • l g := by
  simp [doubleGromov, two_nsmul]

private theorem doubleGromov_one_left (f : G) : doubleGromov l 1 f = 0 := by
  simp [doubleGromov]

private theorem doubleGromov_one_right (g : G) : doubleGromov l g 1 = 0 := by
  simp [doubleGromov]

private theorem doubleGromov_nonneg (g f : G) : 0 ≤ doubleGromov l g f := by
  simpa [doubleGromov, sub_nonneg] using map_mul_le_add l g⁻¹ f

private theorem doubleGromov_le_two_nsmul_left (g f : G) : doubleGromov l g f ≤ 2 • l g :=
  (l.gromovProduct_le_coe_iff (c := l g)).1 (l.gromovProduct_le_left g f)

private theorem doubleGromov_le_two_nsmul_right (g f : G) : doubleGromov l g f ≤ 2 • l f :=
  (l.gromovProduct_le_coe_iff (c := l f)).1 (l.gromovProduct_le_right g f)

private theorem min_doubleGromov_le (g f h : G) :
    min (doubleGromov l g f) (doubleGromov l f h) ≤ doubleGromov l g h := by
  have hyp := l.min_gromovProduct_le g f h
  rcases le_total (l.gromovProduct g f) (l.gromovProduct f h) with hle | hle
  · rw [min_eq_left hle] at hyp
    exact (min_le_left _ _).trans (l.gromovProduct_le_gromovProduct_iff.1 hyp)
  · rw [min_eq_right hle] at hyp
    exact (min_le_right _ _).trans (l.gromovProduct_le_gromovProduct_iff.1 hyp)

end DoubleGromov

/-! ### Carrier and metric of Chiswell's space -/

/-- Raw pairs `(g, s)` with `0 ≤ s ≤ l g`, representing the point at distance `s` from the base
point toward the vertex `g`. -/
private abbrev RawPair (l : LyndonLength G Λ) : Type (max u v) :=
  { p : G × Λ // 0 ≤ p.2 ∧ p.2 ≤ l p.1 }

/-- Two raw pairs represent the same point when they lie at the same distance from the base point
within the common initial segment `[0, c(g, f)]`. -/
private def rawRel (l : LyndonLength G Λ) (p q : RawPair l) : Prop :=
  p.1.2 = q.1.2 ∧ 2 • p.1.2 ≤ doubleGromov l p.1.1 q.1.1

private def rawSetoid (l : LyndonLength G Λ) : Setoid (RawPair l) where
  r := rawRel l
  iseqv :=
    { refl p := ⟨rfl, by rw [doubleGromov_self]; exact nsmul_le_nsmul_right p.2.2 2⟩
      symm := fun ⟨h₁, h₂⟩ => ⟨h₁.symm, by rwa [← h₁, doubleGromov_comm]⟩
      trans := fun {p q r} ⟨h₁, hpq⟩ ⟨h₂, hqr⟩ =>
        ⟨h₁.trans h₂,
          (le_min hpq (h₁ ▸ hqr)).trans (min_doubleGromov_le l p.1.1 q.1.1 r.1.1)⟩ }

/-- Chiswell's `Λ`-metric space attached to a Lyndon length function `l : LyndonLength G Λ`: the
quotient of `{(g, s) : G × Λ | 0 ≤ s ≤ l g}` identifying `(g, s)` with `(f, s)` whenever
`2 • s ≤ l g + l f - l (g⁻¹ * f)`. -/
def Chiswell (l : LyndonLength G Λ) : Type (max u v) :=
  Quotient (rawSetoid l)

variable (l : LyndonLength G Λ)

/-- The point of `l.Chiswell` at distance `s` from the base point toward `g`, for `0 ≤ s ≤ l g`. -/
def chiswellMk (g : G) (s : Λ) (hs₀ : 0 ≤ s) (hs : s ≤ l g) : l.Chiswell :=
  Quotient.mk (rawSetoid l) ⟨(g, s), hs₀, hs⟩

/-- Two pairs `(g, s)` and `(f, t)` represent the same point of `l.Chiswell` if and only if
`s = t` and `2 • s ≤ l g + l f - l (g⁻¹ * f)`. -/
theorem chiswellMk_eq_chiswellMk_iff {g f : G} {s t : Λ} {hs₀ : 0 ≤ s} {hs : s ≤ l g}
    {ht₀ : 0 ≤ t} {ht : t ≤ l f} :
    l.chiswellMk g s hs₀ hs = l.chiswellMk f t ht₀ ht ↔
      s = t ∧ 2 • s ≤ l g + l f - l (g⁻¹ * f) :=
  Quotient.eq (r := rawSetoid l)

/-- The base point `(1, 0)` of `l.Chiswell`. -/
def chiswellBase : l.Chiswell :=
  l.chiswellMk 1 0 le_rfl (by simp)

instance : Nonempty l.Chiswell :=
  ⟨l.chiswellBase⟩

@[simp]
theorem chiswellMk_zero (g : G) :
    l.chiswellMk g 0 le_rfl (apply_nonneg l g) = l.chiswellBase :=
  l.chiswellMk_eq_chiswellMk_iff.2 ⟨rfl, by simp⟩

/-- An induction principle for `l.Chiswell` in terms of `l.chiswellMk`. -/
@[elab_as_elim]
theorem chiswell_inductionOn {motive : l.Chiswell → Prop} (x : l.Chiswell)
    (mk : ∀ (g : G) (s : Λ) (hs₀ : 0 ≤ s) (hs : s ≤ l g), motive (l.chiswellMk g s hs₀ hs)) :
    motive x :=
  Quotient.inductionOn x fun ⟨⟨g, s⟩, hs₀, hs⟩ => mk g s hs₀ hs

/-- Lift a function on raw pairs `(g, s)` (`0 ≤ s ≤ l g`) respecting the Chiswell equivalence
relation to `l.Chiswell`. -/
def chiswellLift {β : Sort*} (f : ∀ (g : G) (s : Λ), 0 ≤ s → s ≤ l g → β)
    (hf : ∀ (g₁ g₂ : G) (s : Λ) (hs₀ : 0 ≤ s) (h₁ : s ≤ l g₁) (h₂ : s ≤ l g₂),
      2 • s ≤ l g₁ + l g₂ - l (g₁⁻¹ * g₂) → f g₁ s hs₀ h₁ = f g₂ s hs₀ h₂) :
    l.Chiswell → β :=
  Quotient.lift (fun p => f p.1.1 p.1.2 p.2.1 p.2.2) fun p q ⟨hst, hle⟩ => by
    cases p with | mk p hp => cases q with | mk q hq =>
    cases p with | mk g₁ s => cases q with | mk g₂ t =>
    subst hst
    exact hf g₁ g₂ s hp.1 hp.2 hq.2 hle

@[simp]
theorem chiswellLift_chiswellMk {β : Sort*} (f : ∀ (g : G) (s : Λ), 0 ≤ s → s ≤ l g → β)
    (hf : ∀ (g₁ g₂ : G) (s : Λ) (hs₀ : 0 ≤ s) (h₁ : s ≤ l g₁) (h₂ : s ≤ l g₂),
      2 • s ≤ l g₁ + l g₂ - l (g₁⁻¹ * g₂) → f g₁ s hs₀ h₁ = f g₂ s hs₀ h₂)
    (g : G) (s : Λ) (hs₀ : 0 ≤ s) (hs : s ≤ l g) :
    l.chiswellLift f hf (l.chiswellMk g s hs₀ hs) = f g s hs₀ hs :=
  (rfl)

/-- The raw distance `s + t - min (2 • s, 2 • t, 2 c(g, f))` between two raw pairs. -/
private def rawDist (p q : RawPair l) : Λ :=
  p.1.2 + q.1.2 - min (2 • p.1.2) (min (2 • q.1.2) (doubleGromov l p.1.1 q.1.1))

private theorem rawDist_comm (p q : RawPair l) : rawDist l p q = rawDist l q p := by
  rw [rawDist, rawDist, doubleGromov_comm l p.1.1 q.1.1]
  grind

private theorem rawDist_eq_zero_iff {p q : RawPair l} :
    rawDist l p q = 0 ↔ rawRel l p q := by
  rw [rawDist, rawRel, two_nsmul, two_nsmul]
  grind

private theorem rawDist_self (p : RawPair l) : rawDist l p p = 0 :=
  (rawDist_eq_zero_iff l).2 ((rawSetoid l).iseqv.refl p)

private theorem rawDist_triangle (p q r : RawPair l) :
    rawDist l p r ≤ rawDist l p q + rawDist l q r := by
  have hul := min_doubleGromov_le l p.1.1 q.1.1 r.1.1
  rw [rawDist, rawDist, rawDist, two_nsmul, two_nsmul, two_nsmul]
  grind

private theorem rawDist_congr {p₁ p₂ q₁ q₂ : RawPair l} (hp : rawRel l p₁ p₂)
    (hq : rawRel l q₁ q₂) : rawDist l p₁ q₁ = rawDist l p₂ q₂ := by
  have hp0 : rawDist l p₁ p₂ = 0 := (rawDist_eq_zero_iff l).2 hp
  have hq0 : rawDist l q₁ q₂ = 0 := (rawDist_eq_zero_iff l).2 hq
  have h₁ := rawDist_triangle l p₁ p₂ q₁
  have h₂ := rawDist_triangle l p₂ q₂ q₁
  have h₃ := rawDist_triangle l p₂ p₁ q₂
  have h₄ := rawDist_triangle l p₁ q₁ q₂
  rw [rawDist_comm l q₂ q₁] at h₂
  rw [rawDist_comm l p₂ p₁] at h₃
  grind

/-- The `Λ`-metric on `l.Chiswell`: the distance between `(g, s)` and `(f, t)` is
`s + t - min (2 • s) (min (2 • t) (l g + l f - l (g⁻¹ * f)))`. -/
def chiswellMetric : LambdaMetric Λ l.Chiswell where
  toFun := Quotient.lift₂ (rawDist l) fun _ _ _ _ hp hq => rawDist_congr l hp hq
  refl' x := Quotient.inductionOn x (rawDist_self l)
  symm' x y := Quotient.inductionOn₂ x y (rawDist_comm l)
  triangle' x y z := Quotient.inductionOn₃ x y z (rawDist_triangle l)
  eq_of_eq_zero' {x y} := Quotient.inductionOn₂ x y fun _ _ h =>
    Quotient.sound ((rawDist_eq_zero_iff l).1 h)

@[simp]
theorem chiswellMetric_chiswellMk (g f : G) (s t : Λ) (hs₀ : 0 ≤ s) (hs : s ≤ l g)
    (ht₀ : 0 ≤ t) (ht : t ≤ l f) :
    l.chiswellMetric (l.chiswellMk g s hs₀ hs) (l.chiswellMk f t ht₀ ht) =
      s + t - min (2 • s) (min (2 • t) (l g + l f - l (g⁻¹ * f))) :=
  (rfl)

@[simp]
theorem chiswellMetric_chiswellBase_chiswellMk (g : G) (s : Λ) (hs₀ : 0 ≤ s) (hs : s ≤ l g) :
    l.chiswellMetric l.chiswellBase (l.chiswellMk g s hs₀ hs) = s := by
  rw [chiswellBase, chiswellMetric_chiswellMk]
  simp [nsmul_nonneg hs₀ 2]

/-! ### Isometric group action on `l.Chiswell` -/

/-- The raw vertex `(h, l h)` corresponding to `h • chiswellBase`. -/
private def vertexRaw (h : G) : RawPair l :=
  ⟨(h, l h), apply_nonneg l h, le_rfl⟩

private theorem rawDist_vertexRaw_left (h : G) (p : RawPair l) :
    rawDist l (vertexRaw l h) p = l h + p.1.2 - min (2 • p.1.2) (doubleGromov l h p.1.1) := by
  have hle := doubleGromov_le_two_nsmul_left l h p.1.1
  rw [rawDist, vertexRaw]
  grind

private theorem rawDist_vertexRaw_one (p : RawPair l) :
    rawDist l (vertexRaw l 1) p = p.1.2 := by
  rw [rawDist_vertexRaw_left, doubleGromov_one_left, map_one_eq_zero, zero_add,
    min_eq_right (nsmul_nonneg p.2.1 2), sub_zero]

/-- Two raw pairs are equivalent if and only if they have the same distance to every vertex
`vertexRaw l h`. Testing `h = 1` recovers the distance from the base point, and testing `h = q.1.1`
recovers the Gromov product bound. -/
private theorem rawRel_iff_forall_rawDist_vertexRaw {p q : RawPair l} :
    rawRel l p q ↔ ∀ h : G, rawDist l (vertexRaw l h) p = rawDist l (vertexRaw l h) q := by
  refine ⟨fun hpq h => rawDist_congr l ((rawSetoid l).iseqv.refl _) hpq, fun hall => ?_⟩
  have hs : p.1.2 = q.1.2 := by
    simpa only [rawDist_vertexRaw_one] using hall 1
  refine ⟨hs, ?_⟩
  have hq := hall q.1.1
  rw [rawDist_vertexRaw_left, rawDist_vertexRaw_left, doubleGromov_self, hs,
    min_eq_left (nsmul_le_nsmul_right q.2.2 2), doubleGromov_comm] at hq
  grind

/-- Left multiplication by `k : G` on raw pairs: along the triangle `1, k, k * g`, the first
`c(k⁻¹, g)` of `[k, k * g]` folds onto `[k, 1]` and the remainder runs along `[1, k * g]`. -/
private def smulRaw (k : G) (p : RawPair l) : RawPair l :=
  if h : 2 • p.1.2 ≤ l k + l p.1.1 - l (k * p.1.1) then
    ⟨(k, l k - p.1.2),
      by
        have htri : l p.1.1 ≤ l k + l (k * p.1.1) := by
          simpa [map_inv_eq_map] using map_mul_le_add l k⁻¹ (k * p.1.1)
        rw [two_nsmul] at h
        grind,
      sub_le_self (l k) p.2.1⟩
  else
    ⟨(k * p.1.1, p.1.2 + l (k * p.1.1) - l p.1.1),
      by
        have htri : l p.1.1 ≤ l k + l (k * p.1.1) := by
          simpa [map_inv_eq_map] using map_mul_le_add l k⁻¹ (k * p.1.1)
        rw [two_nsmul] at h
        grind,
      by
        have := p.2.2
        grind⟩

/-- Equivariance of distances from vertices: `d(h, k • p) = d(k⁻¹ * h, p)` on raw pairs. This
follows from `0`-hyperbolicity of the Gromov products among `k⁻¹`, `k⁻¹ * h`, and `p.1.1`. -/
private theorem rawDist_vertexRaw_smulRaw (k h : G) (p : RawPair l) :
    rawDist l (vertexRaw l h) (smulRaw l k p) = rawDist l (vertexRaw l (k⁻¹ * h)) p := by
  set g := p.1.1
  set s := p.1.2
  have u₁ := min_doubleGromov_le l (k⁻¹ * h) k⁻¹ g
  have u₂ := min_doubleGromov_le l k⁻¹ (k⁻¹ * h) g
  have u₃ := min_doubleGromov_le l k⁻¹ g (k⁻¹ * h)
  rw [doubleGromov_comm l (k⁻¹ * h) k⁻¹] at u₁
  rw [doubleGromov_comm l g (k⁻¹ * h)] at u₃
  have e₁ : doubleGromov l k⁻¹ (k⁻¹ * h) = l k + l (k⁻¹ * h) - l h := by
    simp [doubleGromov, ← mul_assoc]
  have e₂ : doubleGromov l k⁻¹ g = l k + l g - l (k * g) := by
    simp [doubleGromov]
  have e₃ : doubleGromov l h k = l h + l k - l (k⁻¹ * h) := by
    rw [doubleGromov, ← map_inv_eq_map l (h⁻¹ * k), mul_inv_rev, inv_inv]
  have e₄ : doubleGromov l h (k * g) =
      doubleGromov l (k⁻¹ * h) g + l h + l (k * g) - l (k⁻¹ * h) - l g := by
    simp only [doubleGromov, mul_inv_rev, inv_inv, mul_assoc]
    grind
  rw [rawDist_vertexRaw_left, smulRaw]
  split_ifs with hbranch
  · rw [rawDist_vertexRaw_left]
    simp only [two_nsmul] at hbranch ⊢
    grind
  · rw [rawDist_vertexRaw_left]
    simp only [two_nsmul] at hbranch ⊢
    grind

private theorem smulRaw_congr (k : G) {p q : RawPair l} (hpq : rawRel l p q) :
    rawRel l (smulRaw l k p) (smulRaw l k q) :=
  (rawRel_iff_forall_rawDist_vertexRaw l).2 fun h => by
    rw [rawDist_vertexRaw_smulRaw, rawDist_vertexRaw_smulRaw,
      (rawRel_iff_forall_rawDist_vertexRaw l).1 hpq]

/-- Scalar multiplication by `G` on `l.Chiswell`. -/
private def chiswellSMul (k : G) (x : l.Chiswell) : l.Chiswell :=
  Quotient.map (smulRaw l k) (fun _ _ => smulRaw_congr l k) x

private theorem chiswellSMul_one (x : l.Chiswell) : chiswellSMul l 1 x = x :=
  Quotient.inductionOn x fun p => Quotient.sound (s := rawSetoid l) <|
    (rawRel_iff_forall_rawDist_vertexRaw l).2 fun h => by
      rw [rawDist_vertexRaw_smulRaw, inv_one, one_mul]

private theorem chiswellSMul_mul (k₁ k₂ : G) (x : l.Chiswell) :
    chiswellSMul l (k₁ * k₂) x = chiswellSMul l k₁ (chiswellSMul l k₂ x) :=
  Quotient.inductionOn x fun p => Quotient.sound (s := rawSetoid l) <|
    (rawRel_iff_forall_rawDist_vertexRaw l).2 fun h => by
      rw [rawDist_vertexRaw_smulRaw, rawDist_vertexRaw_smulRaw, rawDist_vertexRaw_smulRaw,
        mul_inv_rev, mul_assoc]

private theorem smulRaw_quotientMk (k g : G) (s : Λ) (hs₀ : 0 ≤ s) (hs : s ≤ l g)
    (h₁ : ∀ (_ : 2 • s ≤ l k + l g - l (k * g)), 0 ≤ l k - s)
    (h₂ : ∀ (_ : ¬(2 • s ≤ l k + l g - l (k * g))), 0 ≤ s + l (k * g) - l g)
    (h₃ : ∀ (_ : ¬(2 • s ≤ l k + l g - l (k * g))), s + l (k * g) - l g ≤ l (k * g)) :
    (if h : 2 • s ≤ l k + l g - l (k * g) then
      l.chiswellMk k (l k - s) (h₁ h) (sub_le_self (l k) hs₀)
    else
      l.chiswellMk (k * g) (s + l (k * g) - l g) (h₂ h) (h₃ h)) =
      Quotient.mk (rawSetoid l) (smulRaw l k ⟨(g, s), hs₀, hs⟩) := by
  rw [smulRaw]
  split_ifs <;> rfl

private theorem chiswellLift_smulRaw_eq (k : G)
    (h₁ : ∀ (g : G) (s : Λ), 0 ≤ s → s ≤ l g →
      2 • s ≤ l k + l g - l (k * g) → 0 ≤ l k - s)
    (h₂ : ∀ (g : G) (s : Λ), 0 ≤ s → s ≤ l g →
      ¬(2 • s ≤ l k + l g - l (k * g)) → 0 ≤ s + l (k * g) - l g)
    (h₃ : ∀ (g : G) (s : Λ), 0 ≤ s → s ≤ l g →
      ¬(2 • s ≤ l k + l g - l (k * g)) → s + l (k * g) - l g ≤ l (k * g))
    (hf : _) (x : l.Chiswell) :
    l.chiswellLift
      (fun g s hs₀ hs =>
        if h : 2 • s ≤ l k + l g - l (k * g) then
          l.chiswellMk k (l k - s) (h₁ g s hs₀ hs h) (sub_le_self (l k) hs₀)
        else
          l.chiswellMk (k * g) (s + l (k * g) - l g) (h₂ g s hs₀ hs h) (h₃ g s hs₀ hs h))
      hf x = chiswellSMul l k x := by
  refine chiswell_inductionOn l x fun g s hs₀ hs => ?_
  rw [chiswellLift_chiswellMk, smulRaw_quotientMk l k g s hs₀ hs]
  rfl

instance instMulActionChiswell : MulAction G l.Chiswell where
  smul k := l.chiswellLift
    (fun g s hs₀ hs =>
      if h : 2 • s ≤ l k + l g - l (k * g) then
        l.chiswellMk k (l k - s)
          (by
            have htri : l g ≤ l k + l (k * g) := by
              simpa [map_inv_eq_map] using map_mul_le_add l k⁻¹ (k * g)
            rw [two_nsmul] at h
            grind)
          (sub_le_self (l k) hs₀)
      else
        l.chiswellMk (k * g) (s + l (k * g) - l g)
          (by
            have htri : l g ≤ l k + l (k * g) := by
              simpa [map_inv_eq_map] using map_mul_le_add l k⁻¹ (k * g)
            rw [two_nsmul] at h
            grind)
          (by grind))
    (by
      intro g₁ g₂ s hs₀ h₁ h₂ hle
      rw [smulRaw_quotientMk l k g₁ s hs₀ h₁, smulRaw_quotientMk l k g₂ s hs₀ h₂]
      exact Quotient.sound (s := rawSetoid l) (smulRaw_congr l k ⟨rfl, hle⟩))
  one_smul x := by
    exact (chiswellLift_smulRaw_eq l 1 _ _ _ _ x).trans (chiswellSMul_one l x)
  mul_smul k₁ k₂ x := by
    exact (chiswellLift_smulRaw_eq l (k₁ * k₂) _ _ _ _ x).trans <|
      (chiswellSMul_mul l k₁ k₂ x).trans <|
        (congrArg (chiswellSMul l k₁) (chiswellLift_smulRaw_eq l k₂ _ _ _ _ x).symm).trans
          (chiswellLift_smulRaw_eq l k₁ _ _ _ _ _).symm

private theorem smul_eq_chiswellSMul (k : G) (x : l.Chiswell) :
    k • x = chiswellSMul l k x :=
  chiswellLift_smulRaw_eq l k _ _ _ _ x

private theorem smul_chiswellMk_raw (k g : G) (s : Λ) (hs₀ : 0 ≤ s) (hs : s ≤ l g) :
    k • l.chiswellMk g s hs₀ hs =
      (Quotient.mk (rawSetoid l) (smulRaw l k ⟨(g, s), hs₀, hs⟩) : l.Chiswell) := by
  rw [smul_eq_chiswellSMul]
  rfl

/-- Left multiplication by `k : G` on a point `l.chiswellMk g s hs₀ hs`: along the triangle
`1, k, k * g`, the initial segment `2 • s ≤ l k + l g - l (k * g)` folds onto `[0, l k]` toward
`k`, and the remainder runs along `[0, l (k * g)]` toward `k * g`. -/
theorem smul_chiswellMk (k g : G) (s : Λ) (hs₀ : 0 ≤ s) (hs : s ≤ l g) :
    k • l.chiswellMk g s hs₀ hs =
      if h : 2 • s ≤ l k + l g - l (k * g) then
        l.chiswellMk k (l k - s)
          (by
            have htri : l g ≤ l k + l (k * g) := by
              simpa [map_inv_eq_map] using map_mul_le_add l k⁻¹ (k * g)
            rw [two_nsmul] at h
            grind)
          (sub_le_self (l k) hs₀)
      else
        l.chiswellMk (k * g) (s + l (k * g) - l g)
          (by
            have htri : l g ≤ l k + l (k * g) := by
              simpa [map_inv_eq_map] using map_mul_le_add l k⁻¹ (k * g)
            rw [two_nsmul] at h
            grind)
          (by grind) := by
  rw [smul_chiswellMk_raw, smulRaw]
  split_ifs <;> rfl

theorem smul_chiswellBase (g : G) :
    g • l.chiswellBase = l.chiswellMk g (l g) (apply_nonneg l g) le_rfl := by
  rw [chiswellBase, smul_chiswellMk_raw]
  refine Quotient.sound (s := rawSetoid l) ((rawRel_iff_forall_rawDist_vertexRaw l).2 fun h => ?_)
  have h₁ : rawDist l (vertexRaw l (g⁻¹ * h)) ⟨(1, 0), le_rfl, by simp⟩ = l (h⁻¹ * g) := by
    have hinv : l (g⁻¹ * h) = l (h⁻¹ * g) := by
      rw [← map_inv_eq_map l (g⁻¹ * h), mul_inv_rev, inv_inv]
    rw [rawDist_vertexRaw_left]
    simp [doubleGromov, hinv]
  have h₂ : rawDist l (vertexRaw l h) (vertexRaw l g) = l (h⁻¹ * g) := by
    rw [rawDist_vertexRaw_left, vertexRaw,
      min_eq_right (doubleGromov_le_two_nsmul_right l h g)]
    simp [doubleGromov]
  exact (rawDist_vertexRaw_smulRaw l g h _).trans (h₁.trans h₂.symm)

@[simp]
theorem chiswellMetric_chiswellBase_smul (g : G) :
    l.chiswellMetric l.chiswellBase (g • l.chiswellBase) = l g := by
  rw [smul_chiswellBase, chiswellMetric_chiswellBase_chiswellMk]

private theorem rawDist_smulRaw (k : G) (p q : RawPair l) :
    rawDist l (smulRaw l k p) (smulRaw l k q) = rawDist l p q := by
  set g := p.1.1
  set s := p.1.2
  set f := q.1.1
  set t := q.1.2
  have u₁ := min_doubleGromov_le l g k⁻¹ f
  have u₂ := min_doubleGromov_le l k⁻¹ g f
  have u₃ := min_doubleGromov_le l k⁻¹ f g
  rw [doubleGromov_comm l g k⁻¹] at u₁
  rw [doubleGromov_comm l f g] at u₃
  have e₁ : doubleGromov l k⁻¹ g = l k + l g - l (k * g) := by simp [doubleGromov]
  have e₂ : doubleGromov l k⁻¹ f = l k + l f - l (k * f) := by simp [doubleGromov]
  have ekf : doubleGromov l k (k * f) = l k + l (k * f) - l f := by
    simp [doubleGromov, ← mul_assoc]
  have ekg : doubleGromov l (k * g) k = l (k * g) + l k - l g := by
    rw [doubleGromov_comm, doubleGromov, add_comm (l k)]
    simp [← mul_assoc]
  have ekgf : doubleGromov l (k * g) (k * f) =
      doubleGromov l g f + l (k * g) + l (k * f) - l g - l f := by
    simp only [doubleGromov, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    grind
  have hkk := doubleGromov_self l k
  have := p.2.2
  have := q.2.2
  rw [smulRaw, smulRaw]
  split_ifs with hp hq hq
  · rw [rawDist, rawDist]
    simp only [two_nsmul] at hp hq hkk ⊢
    grind
  · rw [rawDist, rawDist]
    simp only [two_nsmul] at hp hq ⊢
    grind
  · rw [rawDist, rawDist]
    simp only [two_nsmul] at hp hq ⊢
    grind
  · rw [rawDist, rawDist]
    simp only [two_nsmul] at hp hq ⊢
    grind

/-- `G` acts on `l.Chiswell` by isometries of `l.chiswellMetric`. -/
theorem isIsometricAction_chiswellMetric : l.chiswellMetric.IsIsometricAction G :=
  l.chiswellMetric.isIsometricAction_iff.2 fun k x y => by
    rw [smul_eq_chiswellSMul, smul_eq_chiswellSMul]
    exact Quotient.inductionOn₂ x y fun p q => rawDist_smulRaw l k p q

/-! ### Geodesicity and the `Λ`-tree property -/

/-- The ray `[0, l g] → l.Chiswell` from `chiswellBase` to `g • chiswellBase`, clamped outside
`[0, l g]`. -/
private def chiswellRay (g : G) (r : Λ) : l.Chiswell :=
  l.chiswellMk g (max 0 (min r (l g))) (le_max_left 0 _)
    (max_le (apply_nonneg l g) (min_le_right _ _))

private theorem chiswellRay_eq_chiswellMk (g : G) {r : Λ} (hr₀ : 0 ≤ r) (hr : r ≤ l g) :
    chiswellRay l g r = l.chiswellMk g r hr₀ hr := by
  simp only [chiswellRay, min_eq_left hr, max_eq_right hr₀]

private theorem chiswellMetric_chiswellRay_same (g : G) {a b : Λ} (ha : a ∈ Icc 0 (l g))
    (hb : b ∈ Icc 0 (l g)) :
    l.chiswellMetric (chiswellRay l g a) (chiswellRay l g b) = |a - b| := by
  rw [chiswellRay_eq_chiswellMk l g ha.1 ha.2, chiswellRay_eq_chiswellMk l g hb.1 hb.2,
    chiswellMetric_chiswellMk]
  have hgg : l g + l g - l (g⁻¹ * g) = 2 • l g := by simp [two_nsmul]
  rw [hgg, two_nsmul, two_nsmul, two_nsmul]
  rcases le_total a b with hab | hab
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]
    grind [ha.2, hb.2]
  · rw [abs_of_nonneg (sub_nonneg.2 hab)]
    grind [ha.2, hb.2]

private theorem exists_isSegment_chiswellMk_same (g : G) {a b : Λ} (ha₀ : 0 ≤ a) (ha : a ≤ l g)
    (hb₀ : 0 ≤ b) (hb : b ≤ l g) :
    ∃ σ, l.chiswellMetric.IsSegment σ (l.chiswellMk g a ha₀ ha) (l.chiswellMk g b hb₀ hb) := by
  rcases le_total a b with hab | hab
  · have hdist : l.chiswellMetric (l.chiswellMk g a ha₀ ha) (l.chiswellMk g b hb₀ hb) = b - a := by
      rw [← chiswellRay_eq_chiswellMk l g ha₀ ha, ← chiswellRay_eq_chiswellMk l g hb₀ hb,
        chiswellMetric_chiswellRay_same l g ⟨ha₀, ha⟩ ⟨hb₀, hb⟩, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.2 hab)]
    let φ : Λ → l.Chiswell := fun r => chiswellRay l g (a + r)
    refine ⟨_, LambdaMetric.isSegment_iff.2 ⟨φ, ?_, ?_, (LambdaMetric.isometricOn_iff _).2 ?_, rfl⟩⟩
    · simp [φ, chiswellRay_eq_chiswellMk l g ha₀ ha]
    · rw [hdist]
      simp [φ, add_sub_cancel, chiswellRay_eq_chiswellMk l g hb₀ hb]
    · rw [hdist]
      intro u hu v hv
      rw [chiswellMetric_chiswellRay_same l g ⟨by grind, by grind⟩ ⟨by grind, by grind⟩]
      congr 1
      grind
  · have hdist : l.chiswellMetric (l.chiswellMk g a ha₀ ha) (l.chiswellMk g b hb₀ hb) = a - b := by
      rw [← chiswellRay_eq_chiswellMk l g ha₀ ha, ← chiswellRay_eq_chiswellMk l g hb₀ hb,
        chiswellMetric_chiswellRay_same l g ⟨ha₀, ha⟩ ⟨hb₀, hb⟩,
        abs_of_nonneg (sub_nonneg.2 hab)]
    let φ : Λ → l.Chiswell := fun r => chiswellRay l g (a - r)
    refine ⟨_, LambdaMetric.isSegment_iff.2 ⟨φ, ?_, ?_, (LambdaMetric.isometricOn_iff _).2 ?_, rfl⟩⟩
    · simp [φ, chiswellRay_eq_chiswellMk l g ha₀ ha]
    · rw [hdist]
      simp [φ, sub_sub_cancel, chiswellRay_eq_chiswellMk l g hb₀ hb]
    · rw [hdist]
      intro u hu v hv
      rw [chiswellMetric_chiswellRay_same l g ⟨by grind, by grind⟩ ⟨by grind, by grind⟩,
        sub_sub_sub_cancel_left, abs_sub_comm]

/-- Any two points `(g, s)` and `(f, t)` in `l.Chiswell` are joined by a geodesic segment: either
one lies in the common initial segment `2 • r ≤ l g + l f - l (g⁻¹ * f)` so both lie on a single
ray, or the path runs down the `g`-ray and up the `f`-ray across the branch threshold. -/
private theorem exists_isSegment_chiswellMk {g f : G} {s t : Λ} (hs₀ : 0 ≤ s) (hs : s ≤ l g)
    (ht₀ : 0 ≤ t) (ht : t ≤ l f) :
    ∃ σ, l.chiswellMetric.IsSegment σ (l.chiswellMk g s hs₀ hs) (l.chiswellMk f t ht₀ ht) := by
  set D := doubleGromov l g f
  have hD₀ : 0 ≤ D := doubleGromov_nonneg l g f
  have hDg : D ≤ 2 • l g := doubleGromov_le_two_nsmul_left l g f
  have hDf : D ≤ 2 • l f := doubleGromov_le_two_nsmul_right l g f
  by_cases hsD : 2 • s ≤ D
  · have hsf : s ≤ l f := by
      have := hsD.trans hDf
      rw [two_nsmul, two_nsmul] at this
      grind
    have heq : l.chiswellMk g s hs₀ hs = l.chiswellMk f s hs₀ hsf :=
      l.chiswellMk_eq_chiswellMk_iff.2 ⟨rfl, hsD⟩
    rw [heq]
    exact exists_isSegment_chiswellMk_same l f hs₀ hsf ht₀ ht
  by_cases htD : 2 • t ≤ D
  · have htg : t ≤ l g := by
      have := htD.trans hDg
      rw [two_nsmul, two_nsmul] at this
      grind
    have heq : l.chiswellMk f t ht₀ ht = l.chiswellMk g t ht₀ htg :=
      l.chiswellMk_eq_chiswellMk_iff.2 ⟨rfl, by rwa [← doubleGromov, doubleGromov_comm]⟩
    rw [heq]
    exact exists_isSegment_chiswellMk_same l g hs₀ hs ht₀ htg
  have hDs : D < 2 • s := lt_of_not_ge hsD
  have hDt : D < 2 • t := lt_of_not_ge htD
  have hdist : l.chiswellMetric (l.chiswellMk g s hs₀ hs) (l.chiswellMk f t ht₀ ht) =
      s + t - D := by
    rw [chiswellMetric_chiswellMk, ← doubleGromov]
    rw [two_nsmul] at hDs hDt ⊢
    rw [two_nsmul]
    grind
  let φ : Λ → l.Chiswell := fun r =>
    if D ≤ 2 • (s - r) then chiswellRay l g (s - r) else chiswellRay l f (r - s + D)
  refine ⟨_, LambdaMetric.isSegment_iff.2 ⟨φ, ?_, ?_, (LambdaMetric.isometricOn_iff _).2 ?_, rfl⟩⟩
  · simp [φ, hDs.le, chiswellRay_eq_chiswellMk l g hs₀ hs]
  · rw [hdist]
    have hbranch : ¬(D ≤ 2 • (s - (s + t - D))) := by
      rw [two_nsmul] at hDt ⊢
      grind
    have hend : s + t - D - s + D = t := by grind
    simp [φ, hbranch, hend, chiswellRay_eq_chiswellMk l f ht₀ ht]
  · rw [hdist]
    intro a ha b hb
    wlog hab : a ≤ b generalizing a b
    · rw [l.chiswellMetric.symm, abs_sub_comm]
      exact this b hb a ha (le_of_not_ge hab)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]
    simp only [φ]
    split_ifs with ha' hb' hb'
    · rw [chiswellMetric_chiswellRay_same l g
        ⟨by rw [two_nsmul] at ha'; grind, by grind⟩
        ⟨by rw [two_nsmul] at hb'; grind, by grind⟩,
        sub_sub_sub_cancel_left, abs_of_nonneg (sub_nonneg.2 hab)]
    · rw [chiswellRay_eq_chiswellMk l g (by rw [two_nsmul] at ha'; grind) (by grind),
        chiswellRay_eq_chiswellMk l f (by rw [two_nsmul] at hb'; grind) (by grind),
        chiswellMetric_chiswellMk, ← doubleGromov]
      rw [two_nsmul] at ha' hb' ⊢
      rw [two_nsmul]
      grind
    · exfalso
      rw [two_nsmul] at ha' hb'
      grind
    · rw [chiswellMetric_chiswellRay_same l f
        ⟨by rw [two_nsmul] at ha'; grind, by grind⟩
        ⟨by rw [two_nsmul] at hb'; grind, by grind⟩]
      have hdiff : (a - s + D) - (b - s + D) = a - b := by grind
      rw [hdiff, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]

/-- Chiswell's metric `l.chiswellMetric` is geodesic (without assuming axiom (L4)). -/
theorem isGeodesic_chiswellMetric : l.chiswellMetric.IsGeodesic :=
  LambdaMetric.isGeodesic_iff.2 fun x y =>
    chiswell_inductionOn l x fun _ _ hs₀ hs =>
      chiswell_inductionOn l y fun _ _ ht₀ ht =>
        exists_isSegment_chiswellMk l hs₀ hs ht₀ ht

/-- Chiswell's theorem (existence): when the Gromov products of `l` lie in `Λ`, `l.chiswellMetric`
makes `l.Chiswell` a `Λ`-tree. -/
theorem isTree_chiswellMetric
    (hl : ∀ g f : G, ∃ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f) :
    l.chiswellMetric.IsTree := by
  refine LambdaMetric.isTree_of_min_dist_add_dist_sub_dist_le l.chiswellBase
    l.isGeodesic_chiswellMetric
    (fun x y => chiswell_inductionOn l x fun g s hs₀ hs =>
      chiswell_inductionOn l y fun f t ht₀ ht => ?_)
    (fun x y z => chiswell_inductionOn l x fun g s hs₀ hs =>
      chiswell_inductionOn l y fun f t ht₀ ht =>
      chiswell_inductionOn l z fun h u hu₀ hu => ?_)
  · obtain ⟨c, hc⟩ := hl g f
    have hc' := l.coe_eq_gromovProduct_iff.1 hc
    clear hl hc
    refine ⟨min s (min t c), ?_⟩
    rw [chiswellMetric_chiswellBase_chiswellMk, chiswellMetric_chiswellBase_chiswellMk,
      chiswellMetric_chiswellMk, sub_sub_cancel, ← hc']
    have hmono : Monotone (fun a : Λ => 2 • a) := fun _ _ hab => nsmul_le_nsmul_right hab 2
    rw [← hmono.map_min, ← hmono.map_min, two_nsmul]
  · have hul := min_doubleGromov_le l g f h
    simp only [doubleGromov] at hul
    simp only [chiswellMetric_chiswellBase_chiswellMk, chiswellMetric_chiswellMk, sub_sub_cancel]
    grind

/-- At `l.chiswellBase`, the based length function of any `Λ`-tree and isometric action witnesses
on `l.Chiswell` is `l` itself. -/
@[simp]
theorem basedLength_chiswellBase {hd : l.chiswellMetric.IsTree}
    {hG : l.chiswellMetric.IsIsometricAction G} :
    hd.basedLength hG l.chiswellBase = l := by
  ext g
  simp

/-- `l.chiswellMetric` makes `l.Chiswell` a `Λ`-tree if and only if the Gromov products of `l` lie
in `Λ`. -/
theorem isTree_chiswellMetric_iff :
    l.chiswellMetric.IsTree ↔
      ∀ g f : G, ∃ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f :=
  ⟨fun hd =>
      l.basedLength_chiswellBase (hd := hd) (hG := l.isIsometricAction_chiswellMetric) ▸
        hd.exists_coe_eq_gromovProduct_basedLength l.isIsometricAction_chiswellMetric
          l.chiswellBase,
    l.isTree_chiswellMetric⟩

/-- When `l` satisfies (L4), the action of `G` on `l.Chiswell` is free if and only if `l` is a free
Lyndon length function. -/
theorem isFreeAction_chiswell_iff
    (hl : ∀ g f : G, ∃ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f) :
    LambdaMetric.IsFreeAction G l.Chiswell ↔ l.IsFree := by
  rw [← (l.isTree_chiswellMetric hl).isFree_basedLength_iff l.isIsometricAction_chiswellMetric
    l.chiswellBase, l.basedLength_chiswellBase]

/-! ### Universal equivariant isometric embedding and Chiswell's theorem -/

section Embed

variable {l} {X : Type*} [MulAction G X] {d : LambdaMetric Λ X}
  (hd : d.IsTree) (hG : d.IsIsometricAction G) (x₀ : X) (hlen : hd.basedLength hG x₀ = l)
include hd hG hlen

private theorem exists_mem_segment_dist_eq (p : RawPair l) :
    ∃ u ∈ hd.segment x₀ (p.1.1 • x₀), d x₀ u = p.1.2 := by
  have hp : p.1.2 ≤ d x₀ (p.1.1 • x₀) := by
    simpa [← hlen] using p.2.2
  exact (hd.isSegment_segment x₀ (p.1.1 • x₀)).exists_dist_eq
    (hd.left_mem_segment x₀ _) (hd.right_mem_segment x₀ _) p.2.1 hp

private noncomputable def embedRaw (p : RawPair l) : X :=
  (exists_mem_segment_dist_eq hd hG x₀ hlen p).choose

private theorem embedRaw_mem_segment (p : RawPair l) :
    embedRaw hd hG x₀ hlen p ∈ hd.segment x₀ (p.1.1 • x₀) :=
  (exists_mem_segment_dist_eq hd hG x₀ hlen p).choose_spec.1

private theorem dist_embedRaw (p : RawPair l) :
    d x₀ (embedRaw hd hG x₀ hlen p) = p.1.2 :=
  (exists_mem_segment_dist_eq hd hG x₀ hlen p).choose_spec.2

private theorem dist_embedRaw_embedRaw (p q : RawPair l) :
    d (embedRaw hd hG x₀ hlen p) (embedRaw hd hG x₀ hlen q) = rawDist l p q := by
  rw [hd.dist_of_mem_segment (embedRaw_mem_segment hd hG x₀ hlen p)
    (embedRaw_mem_segment hd hG x₀ hlen q), dist_embedRaw, dist_embedRaw,
    ← hG.dist_inv_mul_smul]
  have hg : d x₀ (p.1.1 • x₀) = l p.1.1 := by simp [← hlen]
  have hf : d x₀ (q.1.1 • x₀) = l q.1.1 := by simp [← hlen]
  have hgf : d x₀ ((p.1.1⁻¹ * q.1.1) • x₀) = l (p.1.1⁻¹ * q.1.1) := by simp [← hlen]
  rw [hg, hf, hgf]
  rfl

private theorem embedRaw_vertexRaw (h : G) :
    embedRaw hd hG x₀ hlen (vertexRaw l h) = h • x₀ := by
  refine hd.eq_of_mem_segment_of_dist_eq (embedRaw_mem_segment hd hG x₀ hlen (vertexRaw l h))
    (hd.right_mem_segment x₀ (h • x₀)) ?_
  rw [dist_embedRaw]
  simp [vertexRaw, ← hlen]

/-- For any isometric action of `G` on a `Λ`-tree `X` with base point `x₀` whose based length
function is `l`, `l.Chiswell` embeds `G`-equivariantly and isometrically into `X`, sending
`l.chiswellBase` to `x₀` and having range `⋃ g : G, [x₀, g • x₀]`. -/
noncomputable def chiswellEmbed : l.Chiswell → X :=
  Quotient.lift (embedRaw hd hG x₀ hlen) fun p q hpq =>
    d.eq_zero_iff.1 <| (dist_embedRaw_embedRaw hd hG x₀ hlen p q).trans <|
      (rawDist_eq_zero_iff l).2 hpq

private theorem chiswellEmbed_quotientMk (p : RawPair l) :
    chiswellEmbed hd hG x₀ hlen (Quotient.mk (rawSetoid l) p) = embedRaw hd hG x₀ hlen p :=
  rfl

@[simp]
theorem dist_chiswellEmbed (x y : l.Chiswell) :
    d (chiswellEmbed hd hG x₀ hlen x) (chiswellEmbed hd hG x₀ hlen y) = l.chiswellMetric x y :=
  Quotient.inductionOn₂ x y (dist_embedRaw_embedRaw hd hG x₀ hlen)

theorem chiswellEmbed_injective : Function.Injective (chiswellEmbed hd hG x₀ hlen) := fun x y h =>
  l.chiswellMetric.eq_zero_iff.1 <| by rw [← dist_chiswellEmbed hd hG x₀ hlen, h, d.refl]

@[simp]
theorem chiswellEmbed_chiswellBase : chiswellEmbed hd hG x₀ hlen l.chiswellBase = x₀ := by
  have hv : (Quotient.mk (rawSetoid l) (vertexRaw l 1) : l.Chiswell) = l.chiswellBase :=
    Quotient.sound (s := rawSetoid l) ⟨map_one_eq_zero l, by simp [vertexRaw, doubleGromov]⟩
  rw [← hv, chiswellEmbed_quotientMk, embedRaw_vertexRaw, one_smul]

@[simp]
theorem chiswellEmbed_smul (k : G) (x : l.Chiswell) :
    chiswellEmbed hd hG x₀ hlen (k • x) = k • chiswellEmbed hd hG x₀ hlen x := by
  refine chiswell_inductionOn l x fun g s hs₀ hs => ?_
  let p : RawPair l := ⟨(g, s), hs₀, hs⟩
  rw [smul_chiswellMk_raw, chiswellMk, chiswellEmbed_quotientMk, chiswellEmbed_quotientMk]
  set u := embedRaw hd hG x₀ hlen p
  set q := smulRaw l k p
  set v := embedRaw hd hG x₀ hlen q
  -- For every vertex `h • x₀`, `k • u` and `v` have the same distance to `h • x₀`.
  have hdist (h : G) : d (h • x₀) (k • u) = d (h • x₀) v := by
    calc d (h • x₀) (k • u)
      _ = d ((k⁻¹ * h) • x₀) u := by rw [← hG.dist_smul_smul k⁻¹, inv_smul_smul, mul_smul]
      _ = rawDist l (vertexRaw l (k⁻¹ * h)) p := by
        rw [← embedRaw_vertexRaw hd hG x₀ hlen (k⁻¹ * h), dist_embedRaw_embedRaw]
      _ = rawDist l (vertexRaw l h) q := (rawDist_vertexRaw_smulRaw l k h p).symm
      _ = d (h • x₀) v := by
        rw [← embedRaw_vertexRaw hd hG x₀ hlen h, dist_embedRaw_embedRaw]
  have h₁ : d x₀ (k • u) = d x₀ v := by simpa only [one_smul] using hdist 1
  have h₂ : d (k • u) (q.1.1 • x₀) = d v (q.1.1 • x₀) := by
    rw [d.symm (k • u), d.symm v, hdist q.1.1]
  have hmem : k • u ∈ hd.segment x₀ (q.1.1 • x₀) := by
    rw [hd.mem_segment_iff, h₁, h₂]
    exact (hd.isSegment_segment x₀ (q.1.1 • x₀)).dist_add_dist
      (embedRaw_mem_segment hd hG x₀ hlen q)
  exact (hd.eq_of_mem_segment_of_dist_eq hmem (embedRaw_mem_segment hd hG x₀ hlen q) h₁).symm

/-- The image of `l.chiswellMk g s hs₀ hs` under `chiswellEmbed` lies on the segment
`[x₀, g • x₀]`. -/
theorem chiswellEmbed_chiswellMk_mem_segment (g : G) (s : Λ) (hs₀ : 0 ≤ s) (hs : s ≤ l g) :
    chiswellEmbed hd hG x₀ hlen (l.chiswellMk g s hs₀ hs) ∈ hd.segment x₀ (g • x₀) :=
  embedRaw_mem_segment hd hG x₀ hlen ⟨(g, s), hs₀, hs⟩

/-- `chiswellEmbed` is the unique `G`-equivariant isometric map `l.Chiswell → X` sending
`l.chiswellBase` to `x₀`. -/
theorem chiswellEmbed_unique {f : l.Chiswell → X}
    (hf_dist : ∀ x y : l.Chiswell, d (f x) (f y) = l.chiswellMetric x y)
    (hf_base : f l.chiswellBase = x₀)
    (hf_smul : ∀ (g : G) (x : l.Chiswell), f (g • x) = g • f x) :
    f = chiswellEmbed hd hG x₀ hlen := by
  ext x
  refine chiswell_inductionOn l x fun g s hs₀ hs => ?_
  have hfx₀ : d x₀ (f (l.chiswellMk g s hs₀ hs)) = s := by
    rw [← hf_base, hf_dist, chiswellMetric_chiswellBase_chiswellMk]
  have hfg : d (f (l.chiswellMk g s hs₀ hs)) (g • x₀) = l g - s := by
    rw [← hf_base, ← hf_smul, hf_dist, smul_chiswellBase, chiswellMetric_chiswellMk]
    have hgg : l g + l g - l (g⁻¹ * g) = 2 • l g := by simp [two_nsmul]
    rw [hgg, two_nsmul, two_nsmul]
    grind
  have hmem : f (l.chiswellMk g s hs₀ hs) ∈ hd.segment x₀ (g • x₀) := by
    rw [hd.mem_segment_iff, hfx₀, hfg]
    have hg : d x₀ (g • x₀) = l g := by simp [← hlen]
    rw [hg, add_sub_cancel]
  refine hd.eq_of_mem_segment_of_dist_eq hmem
    (chiswellEmbed_chiswellMk_mem_segment hd hG x₀ hlen g s hs₀ hs) ?_
  have hemb := dist_chiswellEmbed hd hG x₀ hlen l.chiswellBase (l.chiswellMk g s hs₀ hs)
  rw [chiswellEmbed_chiswellBase, chiswellMetric_chiswellBase_chiswellMk] at hemb
  exact hfx₀.trans hemb.symm

/-- The range of `chiswellEmbed` is the union of the segments `[x₀, g • x₀]` in `X`. -/
theorem range_chiswellEmbed :
    range (chiswellEmbed hd hG x₀ hlen) = ⋃ g : G, hd.segment x₀ (g • x₀) := by
  refine Set.ext fun u => ?_
  simp only [mem_range, mem_iUnion]
  refine ⟨?_, fun ⟨g, hu⟩ => ?_⟩
  · rintro ⟨x, rfl⟩
    exact Quotient.inductionOn x fun p => ⟨p.1.1, embedRaw_mem_segment hd hG x₀ hlen p⟩
  · have hs : d x₀ u ≤ l g := by
      have hsum := (hd.isSegment_segment x₀ (g • x₀)).dist_add_dist hu
      have hg : d x₀ (g • x₀) = l g := by simp [← hlen]
      have hnn := d.nonneg u (g • x₀)
      grind
    refine ⟨l.chiswellMk g (d x₀ u) (d.nonneg x₀ u) hs, ?_⟩
    exact hd.eq_of_mem_segment_of_dist_eq
      (embedRaw_mem_segment hd hG x₀ hlen ⟨(g, d x₀ u), d.nonneg x₀ u, hs⟩)
      hu (dist_embedRaw hd hG x₀ hlen _)

end Embed

/-- Chiswell's theorem on based length functions: a Lyndon length function `l : LyndonLength G Λ` is
the based length function of an isometric action of `G` on a `Λ`-tree if and only if its Gromov
products lie in `Λ` (axiom (L4)). -/
theorem exists_basedLength_eq_iff :
    (∃ (X : Type (max u v)) (_ : MulAction G X) (d : LambdaMetric Λ X) (hd : d.IsTree)
      (hG : d.IsIsometricAction G) (x : X), hd.basedLength hG x = l) ↔
      ∀ g f : G, ∃ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f :=
  ⟨fun ⟨_, _, _, hd, hG, x, hlen⟩ => hlen ▸ hd.exists_coe_eq_gromovProduct_basedLength hG x,
    fun hl => ⟨l.Chiswell, inferInstance, l.chiswellMetric, l.isTree_chiswellMetric hl,
      l.isIsometricAction_chiswellMetric, l.chiswellBase, l.basedLength_chiswellBase⟩⟩

/-- Chiswell's theorem on free length functions: a group `G` has a free `Λ`-valued Lyndon length
function if and only if `G` acts freely by isometries on a `Λ`-tree. -/
theorem exists_isFree_iff (G : Type u) (Λ : Type v) [Group G] [AddCommGroup Λ] [LinearOrder Λ]
    [IsOrderedAddMonoid Λ] :
    (∃ l : LyndonLength G Λ, l.IsFree) ↔
      ∃ (X : Type (max u v)) (_ : MulAction G X) (d : LambdaMetric Λ X),
        d.IsTree ∧ d.IsIsometricAction G ∧ LambdaMetric.IsFreeAction G X := by
  refine ⟨fun ⟨l, hl⟩ => ⟨l.Chiswell, inferInstance, l.chiswellMetric,
    l.isTree_chiswellMetric hl.exists_coe_eq_gromovProduct, l.isIsometricAction_chiswellMetric,
    (l.isFreeAction_chiswell_iff hl.exists_coe_eq_gromovProduct).2 hl⟩, ?_⟩
  rintro ⟨X, _, d, hd, hG, hfree⟩
  obtain ⟨x⟩ := hd.nonempty
  exact ⟨hd.basedLength hG x, (hd.isFree_basedLength_iff hG x).2 hfree⟩

end TauCeti.LyndonLength
