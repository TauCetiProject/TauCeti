/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.ProjIcc
public import TauCeti.GroupTheory.LambdaTree.ZeroHyperbolic
public import TauCeti.GroupTheory.LyndonLength.Basic

/-!
# Chiswell's tree of a Lyndon length function

Let `l : G → Λ` be a Lyndon length function, with Gromov products
`c(g, f) = (l g + l f - l (g⁻¹ * f)) / 2`. Chiswell's construction attaches to `l` a `Λ`-metric
space: the quotient of the set of pairs `(g, a)` with `g : G` and `0 ≤ a ≤ l g` by the equivalence
relation

`(g, a) ∼ (f, b)` if and only if `a = b ≤ c(g, f)`,

with the distance

`d (g, a) (f, b) = a + b - 2 min (a, b, c(g, f))`.

One thinks of the class of `(g, a)` as the point at distance `a` from the base point on a segment
of length `l g` from the base point to its translate by `g`; the segments attached to `g` and `f`
are glued along their initial parts of length `c(g, f)`. All pairs `(g, 0)` give the same point,
the *root*, the distance from the root to the class of `(g, a)` is `a`, and each
`a ↦ (g, a)` is an isometric embedding of `[0, l g]`.

Twice the minimum `min (a, b, c(g, f))` lies in `Λ`, so the distance is defined, and is a
`Λ`-metric, for every Lyndon length function. When moreover the Gromov products lie in `Λ`,
axiom (L4), the space is a `Λ`-tree: it is geodesic, since the class of `(g, a)` is joined to that
of `(f, b)` through the class of `(g, m) ∼ (f, m)`, `m = min (a, b, c(g, f))`, and it is
`0`-hyperbolic with respect to the root because the Gromov products of `l` are.

## Main definitions

* `TauCeti.LyndonLength.ChiswellTree l`: the quotient of `{(g, a) | 0 ≤ a ≤ l g}`.
* `TauCeti.LyndonLength.ChiswellTree.mk`: the class of `(g, a)`.
* `TauCeti.LyndonLength.ChiswellTree.root`: the class of the pairs `(g, 0)`.
* `TauCeti.LyndonLength.ChiswellTree.lift`: the function on the quotient induced by a function
  of the pairs that is constant on classes (`ChiswellTree.lift_mk`, `ChiswellTree.lift_unique`).
* `TauCeti.LyndonLength.chiswellMetric l`: the `Λ`-metric of the quotient.

## Main results

* `TauCeti.LyndonLength.ChiswellTree.mk_eq_mk_iff`: the classes of `(g, a)` and `(f, b)` are equal
  if and only if `a = b ≤ c(g, f)`.
* `TauCeti.LyndonLength.chiswellMetric_mk_mk`,
  `TauCeti.LyndonLength.chiswellMetric_mk_mk_of_coe_eq`: the distance between two classes.
* `TauCeti.LyndonLength.chiswellMetric_root_mk`: the class of `(g, a)` is at distance `a` from the
  root; in particular the class of `(g, l g)` is at distance `l g`.
* `TauCeti.LyndonLength.isTree_chiswellMetric`: if the Gromov products of `l` lie in `Λ`, the
  quotient is a `Λ`-tree.
* For the zero length function the quotient is a point (a `Subsingleton` instance).

## References

* I. Chiswell, *Abstract length functions in groups*, Math. Proc. Cambridge Philos. Soc. 80
  (1976), 451–463.
* I. Chiswell, *Introduction to Λ-trees*, World Scientific, 2001, §2.4.
* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-Archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), §7.1, Theorem 23.
-/

public section

namespace TauCeti.LyndonLength

open Set LambdaMetric

variable {G Λ : Type*} [Group G] [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
  (l : LyndonLength G Λ)

/-- The distance of Chiswell's construction on pairs `(g, a)` with `0 ≤ a ≤ l g`, before passing
to the quotient: `a + b - 2 min (a, b, c(g, f))`. -/
private def preDist (p q : (g : G) × Icc (0 : Λ) (l g)) : Λ :=
  p.2 + q.2 - min (2 • (p.2 : Λ)) (min (2 • (q.2 : Λ)) (l p.1 + l q.1 - l (p.1⁻¹ * q.1)))

private theorem preDist_self (p : (g : G) × Icc (0 : Λ) (l g)) : preDist l p p = 0 := by
  have := p.2.2.2
  simp only [preDist, inv_mul_cancel, map_one_eq_zero, sub_zero, two_nsmul]
  grind

private theorem preDist_comm (p q : (g : G) × Icc (0 : Λ) (l g)) :
    preDist l p q = preDist l q p := by
  have : l (p.1⁻¹ * q.1) = l (q.1⁻¹ * p.1) := by
    rw [← map_inv_eq_map l, mul_inv_rev, inv_inv]
  simp only [preDist, two_nsmul, this]
  grind

/-- The pairs are `0`-hyperbolic with respect to the pairs `(g, 0)`, from which `(g, a)` is at
distance `a`: this is the `0`-hyperbolicity of the Gromov products of `l`. -/
private theorem min_add_sub_preDist_le (p q r : (g : G) × Icc (0 : Λ) (l g)) :
    min ((p.2 : Λ) + q.2 - preDist l p q) ((q.2 : Λ) + r.2 - preDist l q r) ≤
      (p.2 : Λ) + r.2 - preDist l p r := by
  simp only [preDist, sub_sub_cancel]
  refine le_min ?_ (le_min ?_ ?_)
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_min ((min_le_right _ _).trans (min_le_right _ _))
      ((min_le_right _ _).trans (min_le_right _ _))).trans
      (l.min_map_add_map_sub_map_le p.1 q.1 r.1)

private theorem sub_le_preDist (p q : (g : G) × Icc (0 : Λ) (l g)) :
    (p.2 : Λ) - q.2 ≤ preDist l p q := by
  simp only [preDist, two_nsmul]
  grind

private theorem preDist_triangle (p q r : (g : G) × Icc (0 : Λ) (l g)) :
    preDist l p r ≤ preDist l p q + preDist l q r := by
  grind [min_add_sub_preDist_le l p q r, sub_le_preDist l p q, sub_le_preDist l r q,
    preDist_comm l r q]

private theorem preDist_eq_zero_iff {p q : (g : G) × Icc (0 : Λ) (l g)} :
    preDist l p q = 0 ↔ (p.2 : Λ) = q.2 ∧ 2 • (p.2 : Λ) ≤ l p.1 + l q.1 - l (p.1⁻¹ * q.1) := by
  simp only [preDist, two_nsmul]
  grind

/-- The equivalence relation of Chiswell's construction: `(g, a) ∼ (f, b)` when their distance
vanishes, that is, when `a = b ≤ c(g, f)`. -/
private def chiswellSetoid : Setoid ((g : G) × Icc (0 : Λ) (l g)) where
  r p q := preDist l p q = 0
  iseqv :=
    { refl := preDist_self l
      symm := fun {p q} h => by rw [preDist_comm, h]
      trans := fun {p q r} hpq hqr => by
        grind [preDist_triangle l p q r, preDist_triangle l p r p, preDist_self l p,
          preDist_comm l p r] }

/-- Chiswell's tree of a Lyndon length function `l : G → Λ`: the quotient of the set of pairs
`(g, a)` with `0 ≤ a ≤ l g` by the relation `(g, a) ∼ (f, b)` if and only if `a = b ≤ c(g, f)`,
where `c` is the Gromov product. With `TauCeti.LyndonLength.chiswellMetric` it is a `Λ`-metric
space, and a `Λ`-tree when the Gromov products of `l` lie in `Λ`
(`TauCeti.LyndonLength.isTree_chiswellMetric`). -/
def ChiswellTree : Type _ :=
  Quotient (chiswellSetoid l)

namespace ChiswellTree

variable {l}

/-- The class of the pair `(g, a)`, for `0 ≤ a ≤ l g`, in Chiswell's tree. -/
def mk (g : G) (a : Icc (0 : Λ) (l g)) : l.ChiswellTree :=
  Quotient.mk (chiswellSetoid l) ⟨g, a⟩

/-- Every point of Chiswell's tree is the class of a pair `(g, a)`. -/
@[elab_as_elim, induction_eliminator]
protected theorem ind {motive : l.ChiswellTree → Prop} (mk : ∀ g a, motive (mk g a))
    (x : l.ChiswellTree) : motive x :=
  Quotient.ind (fun p => mk p.1 p.2) x

/-- The classes of `(g, a)` and `(f, b)` are equal if and only if `a = b ≤ c(g, f)`. -/
theorem mk_eq_mk_iff {g f : G} {a : Icc (0 : Λ) (l g)} {b : Icc (0 : Λ) (l f)} :
    mk g a = mk f b ↔
      (a : Λ) = b ∧ ((a : Λ) : DivisibleHull Λ) ≤ l.gromovProduct g f := by
  rw [coe_le_gromovProduct_iff]
  -- The relation of the quotient is, by definition, the vanishing of `preDist`.
  exact Quotient.eq.trans (preDist_eq_zero_iff l)

section lift

variable {β : Sort*}

/-- A function of the pairs `(g, a)` taking the same value on `(g, a)` and `(f, b)` whenever
`a = b ≤ c(g, f)` descends to a function on Chiswell's tree. -/
def lift (φ : ∀ g : G, Icc (0 : Λ) (l g) → β)
    (hφ : ∀ ⦃g f : G⦄ ⦃a : Icc (0 : Λ) (l g)⦄ ⦃b : Icc (0 : Λ) (l f)⦄, (a : Λ) = b →
      ((a : Λ) : DivisibleHull Λ) ≤ l.gromovProduct g f → φ g a = φ f b) :
    l.ChiswellTree → β :=
  Quotient.lift (fun p => φ p.1 p.2) fun _ _ h =>
    (mk_eq_mk_iff.1 (Quotient.sound h)).elim (hφ · ·)

/-- The function induced by `φ` on Chiswell's tree takes the value `φ g a` at the class
of `(g, a)`. -/
@[simp]
theorem lift_mk (φ : ∀ g : G, Icc (0 : Λ) (l g) → β) (hφ) (g : G) (a : Icc (0 : Λ) (l g)) :
    lift φ hφ (mk g a) = φ g a :=
  (rfl)

/-- A function on Chiswell's tree taking the value `φ g a` at the class of each pair `(g, a)` is
the function induced by `φ`. -/
theorem lift_unique {φ : ∀ g : G, Icc (0 : Λ) (l g) → β} (hφ) {ψ : l.ChiswellTree → β}
    (hψ : ∀ g a, ψ (mk g a) = φ g a) : ψ = lift φ hφ :=
  funext fun x => by induction x with | mk g a => exact hψ g a

end lift

variable (l) in
/-- The root of Chiswell's tree: the common class of the pairs `(g, 0)`. -/
def root : l.ChiswellTree :=
  mk 1 ⟨0, le_rfl, apply_nonneg l 1⟩

instance : Inhabited l.ChiswellTree :=
  ⟨root l⟩

/-- All pairs `(g, 0)` have the same class, the root. -/
@[simp]
theorem mk_zero (g : G) (h : (0 : Λ) ∈ Icc 0 (l g)) : mk g ⟨0, h⟩ = root l :=
  mk_eq_mk_iff.2 ⟨rfl, by simp⟩

/-- Chiswell's tree of the zero length function is a point. -/
instance : Subsingleton (0 : LyndonLength G Λ).ChiswellTree where
  allEq x y := by
    induction x with | mk g a
    induction y with | mk f b
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain rfl : a = 0 := le_antisymm ha.2 ha.1
    obtain rfl : b = 0 := le_antisymm hb.2 hb.1
    rw [mk_zero, mk_zero]

end ChiswellTree

open ChiswellTree

/-- The `Λ`-metric of Chiswell's tree: the distance between the classes of `(g, a)` and `(f, b)`
is `a + b - 2 min (a, b, c(g, f))`, where `c` is the Gromov product
(`TauCeti.LyndonLength.chiswellMetric_mk_mk`). -/
def chiswellMetric : LambdaMetric Λ l.ChiswellTree where
  toFun := Quotient.lift₂ (preDist l) fun p q p' q' (hp : preDist l p p' = 0)
      (hq : preDist l q q' = 0) => by
    grind [preDist_triangle l p p' q, preDist_triangle l p' q' q, preDist_triangle l p' p q',
      preDist_triangle l p q q', preDist_comm l p p', preDist_comm l q q']
  refl' := Quotient.ind (preDist_self l)
  symm' := Quotient.ind₂ (preDist_comm l)
  triangle' x y z := Quotient.inductionOn₃ x y z (preDist_triangle l)
  eq_of_eq_zero' {x y} := Quotient.inductionOn₂ x y fun _ _ h => Quotient.sound h

/-- The distance between the classes of `(g, a)` and `(f, b)` in Chiswell's tree is
`a + b - 2 min (a, b, c(g, f))`; here twice the minimum is written out in `Λ`. -/
theorem chiswellMetric_mk_mk (g f : G) (a : Icc (0 : Λ) (l g)) (b : Icc (0 : Λ) (l f)) :
    l.chiswellMetric (ChiswellTree.mk g a) (ChiswellTree.mk f b) =
      a + b - min (2 • (a : Λ)) (min (2 • (b : Λ)) (l g + l f - l (g⁻¹ * f))) := by
  rfl

/-- The distance between the classes of `(g, a)` and `(f, b)` in Chiswell's tree is
`a + b - 2 min (a, b, c)` when the Gromov product `c = c(g, f)` lies in `Λ`. -/
theorem chiswellMetric_mk_mk_of_coe_eq {g f : G} (a : Icc (0 : Λ) (l g)) (b : Icc (0 : Λ) (l f))
    {c : Λ} (hc : (c : DivisibleHull Λ) = l.gromovProduct g f) :
    l.chiswellMetric (ChiswellTree.mk g a) (ChiswellTree.mk f b) =
      a + b - 2 • min (a : Λ) (min (b : Λ) c) := by
  rw [coe_eq_gromovProduct_iff] at hc
  rw [chiswellMetric_mk_mk, ← hc]
  simp only [two_nsmul]
  grind

/-- The class of `(g, a)` is at distance `a` from the root of Chiswell's tree. -/
@[simp]
theorem chiswellMetric_root_mk (g : G) (a : Icc (0 : Λ) (l g)) :
    l.chiswellMetric (root l) (ChiswellTree.mk g a) = a := by
  have := a.2.1
  simp only [root, chiswellMetric_mk_mk, map_one_eq_zero, inv_one, one_mul, two_nsmul]
  grind

/-- Along the pairs `(g, a)` with `g` fixed, the distance in Chiswell's tree is `|a - b|`. -/
@[simp]
theorem chiswellMetric_mk_mk_self (g : G) (a b : Icc (0 : Λ) (l g)) :
    l.chiswellMetric (ChiswellTree.mk g a) (ChiswellTree.mk g b) = |(a : Λ) - b| := by
  simp only [chiswellMetric_mk_mk, inv_mul_cancel, map_one_eq_zero, sub_zero, two_nsmul]
  grind [a.2.2, b.2.2]

/-! ### Chiswell's tree is a `Λ`-tree -/

/-- Chiswell's tree is `0`-hyperbolic with respect to its root, because the Gromov products of
the length function are `0`-hyperbolic. -/
private theorem min_chiswellMetric_root_le (x y z : l.ChiswellTree) :
    min (l.chiswellMetric (root l) x + l.chiswellMetric (root l) y - l.chiswellMetric x y)
        (l.chiswellMetric (root l) y + l.chiswellMetric (root l) z - l.chiswellMetric y z) ≤
      l.chiswellMetric (root l) x + l.chiswellMetric (root l) z - l.chiswellMetric x z := by
  induction x with | mk g a
  induction y with | mk f b
  induction z with | mk h c
  simp only [chiswellMetric_root_mk, chiswellMetric_mk_mk]
  simpa only [preDist] using min_add_sub_preDist_le l ⟨g, a⟩ ⟨f, b⟩ ⟨h, c⟩

/-- The Gromov products of Chiswell's tree based at its root lie in `Λ` when those of the length
function do. -/
private theorem even_chiswellMetric_root
    (hl : ∀ g f, ∃ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f) (x y : l.ChiswellTree) :
    Even (l.chiswellMetric (root l) x + l.chiswellMetric (root l) y - l.chiswellMetric x y) := by
  induction x with | mk g a
  induction y with | mk f b
  obtain ⟨c, hc⟩ := hl g f
  refine ⟨min (a : Λ) (min (b : Λ) c), ?_⟩
  rw [chiswellMetric_root_mk, chiswellMetric_root_mk, l.chiswellMetric_mk_mk_of_coe_eq a b hc,
    two_nsmul]
  grind

/-- The classes of `(g, s)` and `(g, t)` are joined by a segment of Chiswell's tree, the image
of `[s, t]`. -/
private theorem exists_isSegment_mk (g : G) {s t : Icc (0 : Λ) (l g)} (hst : s ≤ t) :
    ∃ σ, l.chiswellMetric.IsSegment σ (ChiswellTree.mk g s) (ChiswellTree.mk g t) := by
  refine ⟨_, isSegment_iff_exists_Icc.2 ⟨s, t,
    fun r => ChiswellTree.mk g (projIcc 0 (l g) (apply_nonneg l g) r), hst, by simp, by simp, ?_,
    rfl⟩⟩
  refine l.chiswellMetric.isometricOn_iff.2 fun r hr r' hr' => ?_
  have hr₁ : r ∈ Icc 0 (l g) := ⟨s.2.1.trans hr.1, hr.2.trans t.2.2⟩
  have hr₂ : r' ∈ Icc 0 (l g) := ⟨s.2.1.trans hr'.1, hr'.2.trans t.2.2⟩
  rw [chiswellMetric_mk_mk_self, projIcc_of_mem _ hr₁, projIcc_of_mem _ hr₂]

/-- Chiswell's tree is geodesic when the Gromov products of the length function lie in `Λ`: the
classes of `(g, a)` and `(f, b)` are joined through the class of `(g, m) ∼ (f, m)`, where
`m = min (a, b, c(g, f))`. -/
private theorem isGeodesic_chiswellMetric
    (hl : ∀ g f, ∃ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f) :
    l.chiswellMetric.IsGeodesic := by
  refine isGeodesic_iff.2 fun x y => ?_
  induction x with | mk g a
  induction y with | mk f b
  -- `m = min (a, b, c(g, f))`, an element of `Λ` because the Gromov products are.
  obtain ⟨m, hm⟩ := l.even_chiswellMetric_root hl (ChiswellTree.mk g a) (ChiswellTree.mk f b)
  rw [chiswellMetric_root_mk, chiswellMetric_root_mk, chiswellMetric_mk_mk, sub_sub_cancel,
    two_nsmul, two_nsmul] at hm
  have hD := map_mul_le_add l g⁻¹ f
  rw [map_inv_eq_map] at hD
  have hm0 : 0 ≤ m := by grind [a.2.1, b.2.1]
  have hma : m ≤ a := by grind
  have hmb : m ≤ b := by grind
  have hmk : ChiswellTree.mk g ⟨m, hm0, hma.trans a.2.2⟩ =
      ChiswellTree.mk f ⟨m, hm0, hmb.trans b.2.2⟩ :=
    ChiswellTree.mk_eq_mk_iff.2 ⟨rfl, l.coe_le_gromovProduct_iff.2 (by rw [two_nsmul]; grind)⟩
  obtain ⟨σ, hσ⟩ := l.exists_isSegment_mk g (s := ⟨m, hm0, hma.trans a.2.2⟩) (t := a) hma
  obtain ⟨τ, hτ⟩ := l.exists_isSegment_mk f (s := ⟨m, hm0, hmb.trans b.2.2⟩) (t := b) hmb
  rw [← hmk] at hτ
  refine ⟨σ ∪ τ, hσ.symm.union hτ ?_⟩
  nth_rw 2 [hmk]
  rw [chiswellMetric_mk_mk, chiswellMetric_mk_mk_self, chiswellMetric_mk_mk_self, two_nsmul,
    two_nsmul, hm, abs_of_nonneg (sub_nonneg.2 hma), abs_of_nonpos (sub_nonpos.2 hmb)]
  abel

/-- **Chiswell's theorem**, the metric part: the tree of a Lyndon length function whose Gromov
products lie in `Λ`, axiom (L4), is a `Λ`-tree. -/
theorem isTree_chiswellMetric
    (hl : ∀ g f, ∃ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f) :
    l.chiswellMetric.IsTree :=
  (l.isGeodesic_chiswellMetric hl).isTree (root l) (l.even_chiswellMetric_root hl)
    l.min_chiswellMetric_root_le

end TauCeti.LyndonLength
