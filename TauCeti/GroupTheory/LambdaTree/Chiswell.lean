/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.ProjIcc
public import TauCeti.GroupTheory.LambdaTree.Action

/-!
# Chiswell's tree of a Lyndon length function

Let `l : G → Λ` be a Lyndon length function, with Gromov products
`c(g, f) = (l g + l f - l (g⁻¹ * f)) / 2`. Chiswell's construction attaches to `l` a `Λ`-metric
space: the quotient `l.ChiswellTree` of the set of pairs `(g, a)` with `g : G` and `0 ≤ a ≤ l g`
by the equivalence relation

`(g, a) ∼ (f, b)` if and only if `a = b ≤ c(g, f)`,

with the distance

`d (g, a) (f, b) = a + b - 2 min (a, b, c(g, f))`.

One thinks of the class of `(g, a)` as the point at distance `a` from the base point on a segment
of length `l g` from the base point to its translate by `g`; the segments attached to `g` and `f`
are glued along their initial parts of length `c(g, f)`. All pairs `(g, 0)` give the same point,
the *root* (`ChiswellTree.root l`), the distance from the root to the class of `(g, a)` is `a`, and
each `a ↦ (g, a)` is an isometric embedding of `[0, l g]`.

Neither the carrier, the geodesic `Λ`-metric (`TauCeti.LyndonLength.isGeodesic_chiswellMetric`), nor
the isometric `G`-action (`TauCeti.LyndonLength.isIsometricAction_chiswellMetric`) requires axiom
(L4), since all comparisons with `c(g, f)` are stated for the doubled Gromov product
`l g + l f - l (g⁻¹ * f)` in `Λ`. The space `l.ChiswellTree` is a `Λ`-tree, with based length
function `l` at its root, if and only if the Gromov products of `l` lie in `Λ`
(`TauCeti.LyndonLength.isTree_chiswellMetric_iff`).

Moreover, for any isometric action of `G` on a `Λ`-tree `X` with a base point `x₀` whose based
length function is `l`, there is a unique `G`-equivariant isometric embedding `l.chiswellEmbed` of
`l.ChiswellTree` into `X` sending `ChiswellTree.root l` to `x₀`, with range the union of segments
`⋃ g : G, [x₀, g • x₀]`. Combining Chiswell's construction with
`TauCeti.LambdaMetric.IsTree.isFree_basedLength_iff` shows that a group has a free `Λ`-valued
Lyndon length function if and only if it acts freely on a `Λ`-tree
(`TauCeti.LyndonLength.exists_isFree_iff`).

## Main definitions

* `TauCeti.LyndonLength.ChiswellTree l`: the quotient of `{(g, a) | 0 ≤ a ≤ l g}`, equipped with an
  isometric `G`-action.
* `TauCeti.LyndonLength.ChiswellTree.mk`: the class of `(g, a)`.
* `TauCeti.LyndonLength.ChiswellTree.root`: the class of the pairs `(g, 0)`.
* `TauCeti.LyndonLength.ChiswellTree.lift`: the function on the quotient induced by a function
  of the pairs that is constant on classes (`ChiswellTree.lift_mk`, `ChiswellTree.lift_unique`).
* `TauCeti.LyndonLength.chiswellMetric l`: the geodesic `Λ`-metric of the quotient.
* `TauCeti.LyndonLength.chiswellEmbed`: the `G`-equivariant isometric embedding of
  `l.ChiswellTree` onto `⋃ g : G, [x₀, g • x₀]` in any based `G`-`Λ`-tree realising `l`.

## Main results

* `TauCeti.LyndonLength.ChiswellTree.mk_eq_mk_iff`: the classes of `(g, a)` and `(f, b)` are equal
  if and only if `a = b ≤ c(g, f)`.
* `TauCeti.LyndonLength.chiswellMetric_mk_mk`,
  `TauCeti.LyndonLength.chiswellMetric_mk_mk_of_coe_eq`: the distance between two classes.
* `TauCeti.LyndonLength.chiswellMetric_root_mk`: the class of `(g, a)` is at distance `a` from the
  root; in particular `g • root l`, the class of `(g, l g)`, is at distance `l g`
  (`TauCeti.LyndonLength.chiswellMetric_root_smul`).
* `TauCeti.LyndonLength.isGeodesic_chiswellMetric`: `l.chiswellMetric` is geodesic.
* `TauCeti.LyndonLength.isIsometricAction_chiswellMetric`: `G` acts on `l.ChiswellTree` by
  isometries (`TauCeti.LyndonLength.ChiswellTree.smul_mk_of_two_nsmul_le`,
  `TauCeti.LyndonLength.ChiswellTree.smul_mk_of_lt`).
* `TauCeti.LyndonLength.isTree_chiswellMetric`, `TauCeti.LyndonLength.isTree_chiswellMetric_iff`:
  `l.chiswellMetric` is a `Λ`-tree if and only if the Gromov products of `l` lie in `Λ`.
* `TauCeti.LyndonLength.basedLength_chiswellTree_root`: at `ChiswellTree.root l`, the based length
  function of `l.ChiswellTree` is `l`.
* `TauCeti.LyndonLength.isFreeAction_chiswellTree_iff`: when `l` satisfies (L4), the action of `G`
  on `l.ChiswellTree` is free if and only if `l` is free.
* `TauCeti.LyndonLength.chiswellEmbed_unique`, `TauCeti.LyndonLength.range_chiswellEmbed`:
  uniqueness and range of the equivariant isometric embedding.
* `TauCeti.LyndonLength.exists_basedLength_eq_iff`, `TauCeti.LyndonLength.exists_isFree_iff`:
  Chiswell's characterisations of based and free `Λ`-valued Lyndon length functions.
* For the zero length function the quotient is a point (a `Subsingleton` instance).

## References

* I. Chiswell, *Abstract length functions in groups*, Math. Proc. Cambridge Philos. Soc. 80
  (1976), 451–463.
* I. Chiswell, *Introduction to Λ-trees*, World Scientific, 2001, §§2.2, 2.4, and 3.1.
* R. C. Lyndon, *Length functions in groups*, Math. Scand. 12 (1963), 209–234.
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Groups with free regular length
  functions in `ℤⁿ`*, Trans. Amer. Math. Soc. 364 (2012), §2.1, Theorem 1.
* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-Archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), §5 and §7.1, Theorem 23.
-/

public section

namespace TauCeti.LyndonLength

open Set LambdaMetric

universe u v

variable {G : Type u} {Λ : Type v} [Group G] [AddCommGroup Λ] [LinearOrder Λ]
  [IsOrderedAddMonoid Λ] (l : LyndonLength G Λ)

/-- The distance of Chiswell's construction on pairs `(g, a)` with `0 ≤ a ≤ l g`, before passing
to the quotient: `a + b - 2 min (a, b, c(g, f))`. -/
private def preDist (p q : (g : G) × Icc (0 : Λ) (l g)) : Λ :=
  p.2 + q.2 - min (2 • (p.2 : Λ)) (min (2 • (q.2 : Λ)) (l p.1 + l q.1 - l (p.1⁻¹ * q.1)))

private theorem preDist_self (p : (g : G) × Icc (0 : Λ) (l g)) : preDist l p p = 0 := by
  have := p.2.property.2
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

private theorem mk_eq_quotientMk (g : G) (a : Icc (0 : Λ) (l g)) :
    mk g a = (Quotient.mk (chiswellSetoid l) ⟨g, a⟩ : l.ChiswellTree) :=
  (rfl)

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
      a + b - min (2 • (a : Λ)) (min (2 • (b : Λ)) (l g + l f - l (g⁻¹ * f))) :=
  (rfl)

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
  have := a.property.1
  simp only [root, chiswellMetric_mk_mk, map_one_eq_zero, inv_one, one_mul, two_nsmul]
  grind

/-- Along the pairs `(g, a)` with `g` fixed, the distance in Chiswell's tree is `|a - b|`. -/
@[simp]
theorem chiswellMetric_mk_mk_self (g : G) (a b : Icc (0 : Λ) (l g)) :
    l.chiswellMetric (ChiswellTree.mk g a) (ChiswellTree.mk g b) = |(a : Λ) - b| := by
  simp only [chiswellMetric_mk_mk, inv_mul_cancel, map_one_eq_zero, sub_zero, two_nsmul]
  grind [a.property.2, b.property.2]

/-! ### Isometric group action on `l.ChiswellTree` -/

private theorem doubleGromov_comm (g f : G) :
    l g + l f - l (g⁻¹ * f) = l f + l g - l (f⁻¹ * g) :=
  l.gromovProduct_eq_gromovProduct_iff.1 (l.gromovProduct_comm g f)

private theorem doubleGromov_nonneg (g f : G) :
    0 ≤ l g + l f - l (g⁻¹ * f) :=
  sub_nonneg.2 <| by simpa using map_mul_le_add l g⁻¹ f

private theorem doubleGromov_le_two_nsmul_left (g f : G) :
    l g + l f - l (g⁻¹ * f) ≤ 2 • l g :=
  (l.gromovProduct_le_coe_iff (c := l g)).1 (l.gromovProduct_le_left g f)

private theorem doubleGromov_le_two_nsmul_right (g f : G) :
    l g + l f - l (g⁻¹ * f) ≤ 2 • l f :=
  (l.gromovProduct_le_coe_iff (c := l f)).1 (l.gromovProduct_le_right g f)

private theorem map_le_map_add_map_mul (k g : G) : l g ≤ l k + l (k * g) := by
  simpa [map_inv_eq_map] using map_mul_le_add l k⁻¹ (k * g)

private theorem sub_mem_Icc_of_two_nsmul_le {k g : G} {a : Icc (0 : Λ) (l g)}
    (h : 2 • (a : Λ) ≤ l k + l g - l (k * g)) :
    l k - (a : Λ) ∈ Icc 0 (l k) :=
  ⟨by have := map_le_map_add_map_mul l k g; rw [two_nsmul] at h; grind,
    sub_le_self (l k) a.property.1⟩

private theorem add_sub_mem_Icc_of_lt {k g : G} {a : Icc (0 : Λ) (l g)}
    (h : l k + l g - l (k * g) < 2 • (a : Λ)) :
    (a : Λ) + l (k * g) - l g ∈ Icc 0 (l (k * g)) :=
  ⟨by have := map_le_map_add_map_mul l k g; rw [two_nsmul] at h; grind,
    by have := a.property.2; grind⟩

/-- The pair `(h, l h)` representing `h • root l`. -/
private def vertexPair (h : G) : (g : G) × Icc (0 : Λ) (l g) :=
  ⟨h, ⟨l h, apply_nonneg l h, le_rfl⟩⟩

private theorem preDist_vertexPair_left (h : G) (p : (g : G) × Icc (0 : Λ) (l g)) :
    preDist l (vertexPair l h) p =
      l h + p.2 - min (2 • (p.2 : Λ)) (l h + l p.1 - l (h⁻¹ * p.1)) := by
  have hle := doubleGromov_le_two_nsmul_left l h p.1
  simp only [preDist, vertexPair]
  grind

private theorem preDist_vertexPair_one (p : (g : G) × Icc (0 : Λ) (l g)) :
    preDist l (vertexPair l 1) p = p.2 := by
  rw [preDist_vertexPair_left]
  simp [nsmul_nonneg p.2.property.1 2]

/-- Two pairs represent the same point of `l.ChiswellTree` if and only if they have the same
distance to `vertexPair l h` for every `h : G`. -/
private theorem preDist_eq_zero_iff_forall_vertexPair {p q : (g : G) × Icc (0 : Λ) (l g)} :
    preDist l p q = 0 ↔
      ∀ h : G, preDist l (vertexPair l h) p = preDist l (vertexPair l h) q := by
  refine ⟨fun hpq h => ?_, fun hall => ?_⟩
  · grind [preDist_triangle l (vertexPair l h) p q, preDist_triangle l (vertexPair l h) q p,
      preDist_comm l p q]
  · have hs : (p.2 : Λ) = q.2 := by simpa only [preDist_vertexPair_one] using hall 1
    refine (preDist_eq_zero_iff l).2 ⟨hs, ?_⟩
    have hq := hall q.1
    have hqq : l q.1 + l q.1 - l (q.1⁻¹ * q.1) = 2 • l q.1 := by simp [two_nsmul]
    rw [preDist_vertexPair_left, preDist_vertexPair_left, hqq, hs,
      min_eq_left (nsmul_le_nsmul_right q.2.property.2 2), doubleGromov_comm l q.1 p.1] at hq
    grind

/-- Left multiplication by `k : G` on pairs `(g, a)`: along the triangle `1, k, k * g`, the first
`c(k⁻¹, g)` of `[k, k * g]` folds onto `[k, 1]` and the remainder runs along `[1, k * g]`. -/
private def smulPair (k : G) (p : (g : G) × Icc (0 : Λ) (l g)) : (g : G) × Icc (0 : Λ) (l g) :=
  if h : 2 • (p.2 : Λ) ≤ l k + l p.1 - l (k * p.1) then
    ⟨k, ⟨l k - p.2, sub_mem_Icc_of_two_nsmul_le l h⟩⟩
  else
    ⟨k * p.1, ⟨(p.2 : Λ) + l (k * p.1) - l p.1, add_sub_mem_Icc_of_lt l (lt_of_not_ge h)⟩⟩

/-- Equivariance of distances from vertices: `d(h, k • p) = d(k⁻¹ * h, p)` on pairs. -/
private theorem preDist_vertexPair_smulPair (k h : G) (p : (g : G) × Icc (0 : Λ) (l g)) :
    preDist l (vertexPair l h) (smulPair l k p) = preDist l (vertexPair l (k⁻¹ * h)) p := by
  set g := p.1
  have u₁ := l.min_map_add_map_sub_map_le (k⁻¹ * h) k⁻¹ g
  have u₂ := l.min_map_add_map_sub_map_le k⁻¹ (k⁻¹ * h) g
  have u₃ := l.min_map_add_map_sub_map_le k⁻¹ g (k⁻¹ * h)
  rw [doubleGromov_comm l (k⁻¹ * h) k⁻¹] at u₁
  rw [doubleGromov_comm l g (k⁻¹ * h)] at u₃
  have e₁ : l k⁻¹ + l (k⁻¹ * h) - l (k⁻¹⁻¹ * (k⁻¹ * h)) = l k + l (k⁻¹ * h) - l h := by
    simp [← mul_assoc]
  have e₂ : l k⁻¹ + l g - l (k⁻¹⁻¹ * g) = l k + l g - l (k * g) := by simp
  have e₃ : l h + l k - l (h⁻¹ * k) = l h + l k - l (k⁻¹ * h) := by
    rw [← map_inv_eq_map l (h⁻¹ * k), mul_inv_rev, inv_inv]
  have e₄ : l h + l (k * g) - l (h⁻¹ * (k * g)) =
      (l (k⁻¹ * h) + l g - l ((k⁻¹ * h)⁻¹ * g)) + l h + l (k * g) - l (k⁻¹ * h) - l g := by
    simp only [mul_inv_rev, inv_inv, mul_assoc]
    grind
  rw [preDist_vertexPair_left, smulPair]
  split_ifs with hbranch
  · rw [preDist_vertexPair_left]
    simp only [two_nsmul] at hbranch ⊢
    grind
  · rw [preDist_vertexPair_left]
    simp only [two_nsmul] at hbranch ⊢
    grind

private theorem smulPair_congr (k : G) {p q : (g : G) × Icc (0 : Λ) (l g)}
    (hpq : preDist l p q = 0) : preDist l (smulPair l k p) (smulPair l k q) = 0 :=
  (preDist_eq_zero_iff_forall_vertexPair l).2 fun h => by
    rw [preDist_vertexPair_smulPair, preDist_vertexPair_smulPair,
      (preDist_eq_zero_iff_forall_vertexPair l).1 hpq]

namespace ChiswellTree

variable {l}

/-- Left multiplication by `G` on `l.ChiswellTree`. -/
protected def smul (k : G) (x : l.ChiswellTree) : l.ChiswellTree :=
  Quotient.map (smulPair l k) (fun _ _ => smulPair_congr l k) x

instance : SMul G l.ChiswellTree :=
  ⟨ChiswellTree.smul⟩

private theorem smul_mk_eq_quotientMk (k g : G) (a : Icc (0 : Λ) (l g)) :
    k • mk g a = Quotient.mk (chiswellSetoid l) (smulPair l k ⟨g, a⟩) :=
  (rfl)

instance instMulAction : MulAction G l.ChiswellTree where
  one_smul x := by
    refine Quotient.inductionOn x fun p => Quotient.sound <|
      (preDist_eq_zero_iff_forall_vertexPair l).2 fun h => ?_
    rw [preDist_vertexPair_smulPair, inv_one, one_mul]
  mul_smul k₁ k₂ x := by
    refine Quotient.inductionOn x fun p => Quotient.sound <|
      (preDist_eq_zero_iff_forall_vertexPair l).2 fun h => ?_
    rw [preDist_vertexPair_smulPair, preDist_vertexPair_smulPair, preDist_vertexPair_smulPair,
      mul_inv_rev, mul_assoc]

/-- Left multiplication by `k : G` on the class of `(g, a)` in the initial branch
`2 • a ≤ l k + l g - l (k * g)`, which folds onto `[0, l k]` toward `k`. -/
@[simp]
theorem smul_mk_of_two_nsmul_le {k g : G} {a : Icc (0 : Λ) (l g)}
    (h : 2 • (a : Λ) ≤ l k + l g - l (k * g)) :
    k • mk g a = mk k ⟨l k - (a : Λ), by exact sub_mem_Icc_of_two_nsmul_le l h⟩ := by
  rw [smul_mk_eq_quotientMk, smulPair, dite_eq_left h, ← mk_eq_quotientMk]

/-- Left multiplication by `k : G` on the class of `(g, a)` beyond the branch point,
`l k + l g - l (k * g) < 2 • a`, which runs along `[0, l (k * g)]` toward `k * g`. -/
@[simp]
theorem smul_mk_of_lt {k g : G} {a : Icc (0 : Λ) (l g)}
    (h : l k + l g - l (k * g) < 2 • (a : Λ)) :
    k • mk g a = mk (k * g) ⟨(a : Λ) + l (k * g) - l g, by exact add_sub_mem_Icc_of_lt l h⟩ := by
  rw [smul_mk_eq_quotientMk, smulPair, dite_eq_right h.not_ge, ← mk_eq_quotientMk]

/-- Acting by `g : G` sends the root of Chiswell's tree to the class of `(g, l g)`. -/
theorem smul_root (g : G) :
    g • root l = mk g ⟨l g, apply_nonneg l g, le_rfl⟩ := by
  rw [root, smul_mk_of_two_nsmul_le (by simp)]
  simp

end ChiswellTree

/-- The distance between the root and its translate by `g` in Chiswell's tree is `l g`. -/
@[simp]
theorem chiswellMetric_root_smul (g : G) :
    l.chiswellMetric (root l) (g • root l) = l g := by
  rw [ChiswellTree.smul_root, chiswellMetric_root_mk]

private theorem preDist_smulPair (k : G) (p q : (g : G) × Icc (0 : Λ) (l g)) :
    preDist l (smulPair l k p) (smulPair l k q) = preDist l p q := by
  rcases p with ⟨g, ⟨s, hs₀, hs⟩⟩
  rcases q with ⟨f, ⟨t, ht₀, ht⟩⟩
  have u₁ := l.min_map_add_map_sub_map_le g k⁻¹ f
  have u₂ := l.min_map_add_map_sub_map_le k⁻¹ g f
  have u₃ := l.min_map_add_map_sub_map_le k⁻¹ f g
  rw [doubleGromov_comm l g k⁻¹] at u₁
  rw [doubleGromov_comm l f g] at u₃
  have e₁ : l k⁻¹ + l g - l (k⁻¹⁻¹ * g) = l k + l g - l (k * g) := by simp
  have e₂ : l k⁻¹ + l f - l (k⁻¹⁻¹ * f) = l k + l f - l (k * f) := by simp
  have ekf : l k + l (k * f) - l (k⁻¹ * (k * f)) = l k + l (k * f) - l f := by simp [← mul_assoc]
  have ekg : l (k * g) + l k - l ((k * g)⁻¹ * k) = l (k * g) + l k - l g := by
    rw [doubleGromov_comm l (k * g) k, add_comm (l k)]
    simp [← mul_assoc]
  have ekgf : l (k * g) + l (k * f) - l ((k * g)⁻¹ * (k * f)) =
      (l g + l f - l (g⁻¹ * f)) + l (k * g) + l (k * f) - l g - l f := by
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    grind
  have hkk : l k + l k - l (k⁻¹ * k) = 2 • l k := by simp [two_nsmul]
  rw [smulPair, smulPair]
  split_ifs with hp hq hq
  · simp only [preDist, two_nsmul] at hp hq hkk ⊢
    grind
  · simp only [preDist, two_nsmul] at hp hq ⊢
    grind
  · simp only [preDist, two_nsmul] at hp hq ⊢
    grind
  · simp only [preDist, two_nsmul] at hp hq ⊢
    grind

/-- `G` acts on `l.ChiswellTree` by isometries of `l.chiswellMetric`. -/
theorem isIsometricAction_chiswellMetric : l.chiswellMetric.IsIsometricAction G :=
  l.chiswellMetric.isIsometricAction_iff.2 fun k x y => by
    induction x with | mk g a =>
    induction y with | mk f b =>
    rw [smul_mk_eq_quotientMk, smul_mk_eq_quotientMk, mk_eq_quotientMk, mk_eq_quotientMk]
    exact preDist_smulPair l k ⟨g, a⟩ ⟨f, b⟩

/-! ### Geodesicity and the `Λ`-tree property -/

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

/-- The ray `r ↦ mk g (projIcc 0 (l g) _ r)` into Chiswell's tree. -/
private def chiswellRay (g : G) (r : Λ) : l.ChiswellTree :=
  ChiswellTree.mk g (projIcc 0 (l g) (apply_nonneg l g) r)

private theorem chiswellRay_of_mem (g : G) {r : Λ} (hr : r ∈ Icc 0 (l g)) :
    chiswellRay l g r = ChiswellTree.mk g ⟨r, hr⟩ := by
  simp [chiswellRay, projIcc_of_mem _ hr]

private theorem chiswellMetric_chiswellRay_self (g : G) {a b : Λ} (ha : a ∈ Icc 0 (l g))
    (hb : b ∈ Icc 0 (l g)) :
    l.chiswellMetric (chiswellRay l g a) (chiswellRay l g b) = |a - b| := by
  rw [chiswellRay, chiswellRay, chiswellMetric_mk_mk_self, projIcc_of_mem _ ha,
    projIcc_of_mem _ hb]

/-- The classes of `(g, s)` and `(g, t)` with `s ≤ t` are joined by a segment of Chiswell's tree,
the image of `[s, t]`. -/
private theorem exists_isSegment_mk (g : G) {s t : Icc (0 : Λ) (l g)} (hst : s ≤ t) :
    ∃ σ, l.chiswellMetric.IsSegment σ (ChiswellTree.mk g s) (ChiswellTree.mk g t) := by
  refine ⟨_, isSegment_iff_exists_Icc.2 ⟨s, t, chiswellRay l g, hst,
    by simp [chiswellRay], by simp [chiswellRay], ?_, rfl⟩⟩
  refine l.chiswellMetric.isometricOn_iff.2 fun r hr r' hr' =>
    chiswellMetric_chiswellRay_self l g ⟨s.property.1.trans hr.1, hr.2.trans t.property.2⟩
      ⟨s.property.1.trans hr'.1, hr'.2.trans t.property.2⟩

private theorem exists_isSegment_mk_self (g : G) (s t : Icc (0 : Λ) (l g)) :
    ∃ σ, l.chiswellMetric.IsSegment σ (ChiswellTree.mk g s) (ChiswellTree.mk g t) := by
  rcases le_total s t with hst | hts
  · exact l.exists_isSegment_mk g hst
  · obtain ⟨σ, hσ⟩ := l.exists_isSegment_mk g hts
    exact ⟨σ, hσ.symm⟩

private theorem exists_isSegment_mk_of_lt {g f : G} {s : Icc (0 : Λ) (l g)}
    {t : Icc (0 : Λ) (l f)} (hDs : l g + l f - l (g⁻¹ * f) < 2 • (s : Λ))
    (hDt : l g + l f - l (g⁻¹ * f) < 2 • (t : Λ)) :
    ∃ σ, l.chiswellMetric.IsSegment σ (ChiswellTree.mk g s) (ChiswellTree.mk f t) := by
  set D := l g + l f - l (g⁻¹ * f)
  have hD₀ : 0 ≤ D := doubleGromov_nonneg l g f
  have hs₀ := s.property.1; have hs := s.property.2
  have ht₀ := t.property.1; have ht := t.property.2
  have hdist : l.chiswellMetric (ChiswellTree.mk g s) (ChiswellTree.mk f t) = s + t - D := by
    rw [chiswellMetric_mk_mk, two_nsmul, two_nsmul]
    rw [two_nsmul] at hDs hDt
    grind
  let φ : Λ → l.ChiswellTree := fun r =>
    if D ≤ 2 • ((s : Λ) - r) then chiswellRay l g (s - r) else chiswellRay l f (r - s + D)
  refine ⟨_, l.chiswellMetric.isSegment_iff.2 ⟨φ, ?_, ?_, l.chiswellMetric.isometricOn_iff.2 ?_,
    rfl⟩⟩
  · simp [φ, hDs.le, chiswellRay_of_mem l g s.property]
  · rw [hdist]
    have hbranch : ¬(D ≤ 2 • ((s : Λ) - ((s : Λ) + t - D))) := by
      rw [two_nsmul] at hDt ⊢; grind
    have hend : (s : Λ) + t - D - s + D = t := by grind
    simp [φ, hbranch, hend, chiswellRay_of_mem l f t.property]
  · rw [hdist]
    intro a ha b hb
    wlog hab : a ≤ b generalizing a b
    · rw [l.chiswellMetric.symm, abs_sub_comm]
      exact this b hb a ha (le_of_not_ge hab)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]
    simp only [φ]
    split_ifs with ha' hb' hb'
    · rw [chiswellMetric_chiswellRay_self l g ⟨by rw [two_nsmul] at ha'; grind, by grind⟩
          ⟨by rw [two_nsmul] at hb'; grind, by grind⟩,
        sub_sub_sub_cancel_left, abs_of_nonneg (sub_nonneg.2 hab)]
    · have hmem_a : (s : Λ) - a ∈ Icc 0 (l g) := ⟨by rw [two_nsmul] at ha'; grind, by grind⟩
      have hmem_b : b - (s : Λ) + D ∈ Icc 0 (l f) := ⟨by rw [two_nsmul] at hb'; grind, by grind⟩
      rw [chiswellRay_of_mem l g hmem_a, chiswellRay_of_mem l f hmem_b, chiswellMetric_mk_mk]
      simp only [two_nsmul] at ha' hb' ⊢
      grind
    · exfalso; rw [two_nsmul] at ha' hb'; grind
    · rw [chiswellMetric_chiswellRay_self l f ⟨by rw [two_nsmul] at ha'; grind, by grind⟩
        ⟨by rw [two_nsmul] at hb'; grind, by grind⟩]
      have hdiff : (a - s + D) - (b - s + D) = a - b := by grind
      rw [hdiff, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]

/-- Chiswell's metric `l.chiswellMetric` is geodesic (without assuming axiom (L4)). -/
theorem isGeodesic_chiswellMetric : l.chiswellMetric.IsGeodesic := by
  refine isGeodesic_iff.2 fun x y => ?_
  induction x with | mk g s
  induction y with | mk f t
  set D := l g + l f - l (g⁻¹ * f)
  by_cases hsD : 2 • (s : Λ) ≤ D
  · have hsf : (s : Λ) ≤ l f := by
      have := hsD.trans (doubleGromov_le_two_nsmul_right l g f)
      rw [two_nsmul, two_nsmul] at this; grind
    have heq : ChiswellTree.mk g s = ChiswellTree.mk f ⟨(s : Λ), s.property.1, hsf⟩ :=
      ChiswellTree.mk_eq_mk_iff.2 ⟨rfl, l.coe_le_gromovProduct_iff.2 hsD⟩
    rw [heq]
    exact l.exists_isSegment_mk_self f _ t
  by_cases htD : 2 • (t : Λ) ≤ D
  · have htg : (t : Λ) ≤ l g := by
      have := htD.trans (doubleGromov_le_two_nsmul_left l g f)
      rw [two_nsmul, two_nsmul] at this; grind
    have heq : ChiswellTree.mk f t = ChiswellTree.mk g ⟨(t : Λ), t.property.1, htg⟩ :=
      ChiswellTree.mk_eq_mk_iff.2
        ⟨rfl, l.coe_le_gromovProduct_iff.2 (by rwa [doubleGromov_comm l f g])⟩
    rw [heq]
    exact l.exists_isSegment_mk_self g s _
  exact exists_isSegment_mk_of_lt l (lt_of_not_ge hsD) (lt_of_not_ge htD)

/-- **Chiswell's theorem**, the metric part: the tree of a Lyndon length function whose Gromov
products lie in `Λ`, axiom (L4), is a `Λ`-tree. -/
theorem isTree_chiswellMetric
    (hl : ∀ g f, ∃ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f) :
    l.chiswellMetric.IsTree :=
  l.isGeodesic_chiswellMetric.isTree (root l) (l.even_chiswellMetric_root hl)
    l.min_chiswellMetric_root_le

/-- At `ChiswellTree.root l`, the based length function of any `Λ`-tree and isometric action
witnesses on `l.ChiswellTree` is `l` itself. -/
@[simp]
theorem basedLength_chiswellTree_root {hd : l.chiswellMetric.IsTree}
    {hG : l.chiswellMetric.IsIsometricAction G} :
    hd.basedLength hG (root l) = l := by
  ext g
  simp

/-- `l.chiswellMetric` makes `l.ChiswellTree` a `Λ`-tree if and only if the Gromov products of `l`
lie in `Λ`. -/
theorem isTree_chiswellMetric_iff :
    l.chiswellMetric.IsTree ↔
      ∀ g f : G, ∃ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f :=
  ⟨fun hd =>
      l.basedLength_chiswellTree_root (hd := hd) (hG := l.isIsometricAction_chiswellMetric) ▸
        hd.exists_coe_eq_gromovProduct_basedLength l.isIsometricAction_chiswellMetric (root l),
    l.isTree_chiswellMetric⟩

/-- When `l` satisfies (L4), the action of `G` on `l.ChiswellTree` is free if and only if `l` is a
free Lyndon length function. -/
theorem isFreeAction_chiswellTree_iff
    (hl : ∀ g f : G, ∃ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f) :
    LambdaMetric.IsFreeAction G l.ChiswellTree ↔ l.IsFree := by
  rw [← (l.isTree_chiswellMetric hl).isFree_basedLength_iff l.isIsometricAction_chiswellMetric
    (root l), l.basedLength_chiswellTree_root]

/-! ### Universal equivariant isometric embedding and Chiswell's theorem -/

section Embed

variable {l} {X : Type*} [MulAction G X] {d : LambdaMetric Λ X}
  (hd : d.IsTree) (hG : d.IsIsometricAction G) (x₀ : X) (hlen : hd.basedLength hG x₀ = l)
include hd hG hlen

private theorem exists_mem_segment_dist_eq (p : (g : G) × Icc (0 : Λ) (l g)) :
    ∃ u ∈ hd.segment x₀ (p.1 • x₀), d x₀ u = p.2 := by
  have hp : (p.2 : Λ) ≤ d x₀ (p.1 • x₀) := by simpa [← hlen] using p.2.property.2
  exact (hd.isSegment_segment x₀ (p.1 • x₀)).exists_dist_eq
    (hd.left_mem_segment x₀ _) (hd.right_mem_segment x₀ _) p.2.property.1 hp

private noncomputable def embedPair (p : (g : G) × Icc (0 : Λ) (l g)) : X :=
  (exists_mem_segment_dist_eq hd hG x₀ hlen p).choose

private theorem embedPair_mem_segment (p : (g : G) × Icc (0 : Λ) (l g)) :
    embedPair hd hG x₀ hlen p ∈ hd.segment x₀ (p.1 • x₀) :=
  (exists_mem_segment_dist_eq hd hG x₀ hlen p).choose_spec.1

private theorem dist_embedPair (p : (g : G) × Icc (0 : Λ) (l g)) :
    d x₀ (embedPair hd hG x₀ hlen p) = p.2 :=
  (exists_mem_segment_dist_eq hd hG x₀ hlen p).choose_spec.2

private theorem dist_embedPair_embedPair (p q : (g : G) × Icc (0 : Λ) (l g)) :
    d (embedPair hd hG x₀ hlen p) (embedPair hd hG x₀ hlen q) = preDist l p q := by
  rw [hd.dist_of_mem_segment (embedPair_mem_segment hd hG x₀ hlen p)
    (embedPair_mem_segment hd hG x₀ hlen q), dist_embedPair, dist_embedPair,
    ← hG.dist_inv_mul_smul]
  have hg : d x₀ (p.1 • x₀) = l p.1 := by simp [← hlen]
  have hf : d x₀ (q.1 • x₀) = l q.1 := by simp [← hlen]
  have hgf : d x₀ ((p.1⁻¹ * q.1) • x₀) = l (p.1⁻¹ * q.1) := by simp [← hlen]
  rw [hg, hf, hgf, preDist]

private theorem embedPair_vertexPair (h : G) :
    embedPair hd hG x₀ hlen (vertexPair l h) = h • x₀ := by
  refine hd.eq_of_mem_segment_of_dist_eq (embedPair_mem_segment hd hG x₀ hlen (vertexPair l h))
    (hd.right_mem_segment x₀ (h • x₀)) ?_
  rw [dist_embedPair]
  simp [vertexPair, ← hlen]

/-- For any isometric action of `G` on a `Λ`-tree `X` with base point `x₀` whose based length
function is `l`, `l.ChiswellTree` embeds `G`-equivariantly and isometrically into `X`, sending
`ChiswellTree.root l` to `x₀` and having range `⋃ g : G, [x₀, g • x₀]`. -/
noncomputable def chiswellEmbed : l.ChiswellTree → X :=
  Quotient.lift (embedPair hd hG x₀ hlen) fun p q hpq =>
    d.eq_zero_iff.1 <| (dist_embedPair_embedPair hd hG x₀ hlen p q).trans hpq

private theorem chiswellEmbed_quotientMk (p : (g : G) × Icc (0 : Λ) (l g)) :
    chiswellEmbed hd hG x₀ hlen (Quotient.mk (chiswellSetoid l) p) =
      embedPair hd hG x₀ hlen p :=
  (rfl)

@[simp]
theorem dist_chiswellEmbed (x y : l.ChiswellTree) :
    d (chiswellEmbed hd hG x₀ hlen x) (chiswellEmbed hd hG x₀ hlen y) = l.chiswellMetric x y :=
  Quotient.inductionOn₂ x y (dist_embedPair_embedPair hd hG x₀ hlen)

theorem chiswellEmbed_injective : Function.Injective (chiswellEmbed hd hG x₀ hlen) := fun x y h =>
  l.chiswellMetric.eq_zero_iff.1 <| by rw [← dist_chiswellEmbed hd hG x₀ hlen, h, d.refl]

@[simp]
theorem chiswellEmbed_root : chiswellEmbed hd hG x₀ hlen (root l) = x₀ := by
  have hv : (Quotient.mk (chiswellSetoid l) (vertexPair l 1) : l.ChiswellTree) = root l :=
    Quotient.sound ((preDist_eq_zero_iff l).2 ⟨map_one_eq_zero l, by simp [vertexPair]⟩)
  rw [← hv, chiswellEmbed_quotientMk, embedPair_vertexPair, one_smul]

@[simp]
theorem chiswellEmbed_smul (k : G) (x : l.ChiswellTree) :
    chiswellEmbed hd hG x₀ hlen (k • x) = k • chiswellEmbed hd hG x₀ hlen x := by
  induction x with | mk g a =>
  let p : (g : G) × Icc (0 : Λ) (l g) := ⟨g, a⟩
  rw [smul_mk_eq_quotientMk, mk_eq_quotientMk, chiswellEmbed_quotientMk, chiswellEmbed_quotientMk]
  set u := embedPair hd hG x₀ hlen p
  set q := smulPair l k p
  set v := embedPair hd hG x₀ hlen q
  have hdist (h : G) : d (h • x₀) (k • u) = d (h • x₀) v := by
    calc d (h • x₀) (k • u)
      _ = d ((k⁻¹ * h) • x₀) u := by rw [← hG.dist_smul_smul k⁻¹, inv_smul_smul, mul_smul]
      _ = preDist l (vertexPair l (k⁻¹ * h)) p := by
        rw [← embedPair_vertexPair hd hG x₀ hlen (k⁻¹ * h), dist_embedPair_embedPair]
      _ = preDist l (vertexPair l h) q := (preDist_vertexPair_smulPair l k h p).symm
      _ = d (h • x₀) v := by
        rw [← embedPair_vertexPair hd hG x₀ hlen h, dist_embedPair_embedPair]
  have h₁ : d x₀ (k • u) = d x₀ v := by simpa only [one_smul] using hdist 1
  have h₂ : d (k • u) (q.1 • x₀) = d v (q.1 • x₀) := by
    rw [d.symm (k • u), d.symm v, hdist q.1]
  have hmem : k • u ∈ hd.segment x₀ (q.1 • x₀) := by
    rw [hd.mem_segment_iff, h₁, h₂]
    exact (hd.isSegment_segment x₀ (q.1 • x₀)).dist_add_dist
      (embedPair_mem_segment hd hG x₀ hlen q)
  exact (hd.eq_of_mem_segment_of_dist_eq hmem (embedPair_mem_segment hd hG x₀ hlen q) h₁).symm

/-- The image of `ChiswellTree.mk g a` under `chiswellEmbed` lies on the segment `[x₀, g • x₀]`. -/
theorem chiswellEmbed_mk_mem_segment (g : G) (a : Icc (0 : Λ) (l g)) :
    chiswellEmbed hd hG x₀ hlen (ChiswellTree.mk g a) ∈ hd.segment x₀ (g • x₀) :=
  embedPair_mem_segment hd hG x₀ hlen ⟨g, a⟩

/-- `chiswellEmbed` is the unique `G`-equivariant isometric map `l.ChiswellTree → X` sending
`ChiswellTree.root l` to `x₀`. -/
theorem chiswellEmbed_unique {f : l.ChiswellTree → X}
    (hf_dist : ∀ x y : l.ChiswellTree, d (f x) (f y) = l.chiswellMetric x y)
    (hf_root : f (root l) = x₀)
    (hf_smul : ∀ (g : G) (x : l.ChiswellTree), f (g • x) = g • f x) :
    f = chiswellEmbed hd hG x₀ hlen := by
  ext x
  induction x with | mk g a =>
  have hfx₀ : d x₀ (f (ChiswellTree.mk g a)) = a := by
    rw [← hf_root, hf_dist, chiswellMetric_root_mk]
  have hfg : d (f (ChiswellTree.mk g a)) (g • x₀) = l g - a := by
    rw [← hf_root, ← hf_smul, hf_dist, ChiswellTree.smul_root, chiswellMetric_mk_mk_self,
      abs_sub_comm, abs_of_nonneg (sub_nonneg.2 a.property.2)]
  have hmem : f (ChiswellTree.mk g a) ∈ hd.segment x₀ (g • x₀) := by
    rw [hd.mem_segment_iff, hfx₀, hfg]
    have hg : d x₀ (g • x₀) = l g := by simp [← hlen]
    rw [hg, add_sub_cancel]
  refine hd.eq_of_mem_segment_of_dist_eq hmem (chiswellEmbed_mk_mem_segment hd hG x₀ hlen g a) ?_
  have hemb := dist_chiswellEmbed hd hG x₀ hlen (root l) (ChiswellTree.mk g a)
  rw [chiswellEmbed_root, chiswellMetric_root_mk] at hemb
  exact hfx₀.trans hemb.symm

/-- The range of `chiswellEmbed` is the union of the segments `[x₀, g • x₀]` in `X`. -/
theorem range_chiswellEmbed :
    range (chiswellEmbed hd hG x₀ hlen) = ⋃ g : G, hd.segment x₀ (g • x₀) := by
  refine Set.ext fun u => ?_
  simp only [mem_range, mem_iUnion]
  refine ⟨?_, fun ⟨g, hu⟩ => ?_⟩
  · rintro ⟨x, rfl⟩
    exact Quotient.inductionOn x fun p => ⟨p.1, embedPair_mem_segment hd hG x₀ hlen p⟩
  · have hs : d x₀ u ≤ l g := by
      have hsum := (hd.isSegment_segment x₀ (g • x₀)).dist_add_dist hu
      have hg : d x₀ (g • x₀) = l g := by simp [← hlen]
      have hnn := d.nonneg u (g • x₀)
      grind
    refine ⟨ChiswellTree.mk g ⟨d x₀ u, d.nonneg x₀ u, hs⟩, ?_⟩
    exact hd.eq_of_mem_segment_of_dist_eq
      (embedPair_mem_segment hd hG x₀ hlen ⟨g, ⟨d x₀ u, d.nonneg x₀ u, hs⟩⟩)
      hu (dist_embedPair hd hG x₀ hlen _)

end Embed

/-- Chiswell's theorem on based length functions: a Lyndon length function `l : LyndonLength G Λ` is
the based length function of an isometric action of `G` on a `Λ`-tree if and only if its Gromov
products lie in `Λ` (axiom (L4)). -/
theorem exists_basedLength_eq_iff :
    (∃ (X : Type (max u v)) (_ : MulAction G X) (d : LambdaMetric Λ X) (hd : d.IsTree)
      (hG : d.IsIsometricAction G) (x : X), hd.basedLength hG x = l) ↔
      ∀ g f : G, ∃ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f :=
  ⟨fun ⟨_, _, _, hd, hG, x, hlen⟩ => hlen ▸ hd.exists_coe_eq_gromovProduct_basedLength hG x,
    fun hl => ⟨l.ChiswellTree, inferInstance, l.chiswellMetric, l.isTree_chiswellMetric hl,
      l.isIsometricAction_chiswellMetric, root l, l.basedLength_chiswellTree_root⟩⟩

/-- Chiswell's theorem on free length functions: a group `G` has a free `Λ`-valued Lyndon length
function if and only if `G` acts freely by isometries on a `Λ`-tree. -/
theorem exists_isFree_iff (G : Type u) (Λ : Type v) [Group G] [AddCommGroup Λ] [LinearOrder Λ]
    [IsOrderedAddMonoid Λ] :
    (∃ l : LyndonLength G Λ, l.IsFree) ↔
      ∃ (X : Type (max u v)) (_ : MulAction G X) (d : LambdaMetric Λ X),
        d.IsTree ∧ d.IsIsometricAction G ∧ LambdaMetric.IsFreeAction G X := by
  refine ⟨fun ⟨l, hl⟩ => ⟨l.ChiswellTree, inferInstance, l.chiswellMetric,
    l.isTree_chiswellMetric hl.exists_coe_eq_gromovProduct, l.isIsometricAction_chiswellMetric,
    (l.isFreeAction_chiswellTree_iff hl.exists_coe_eq_gromovProduct).2 hl⟩, ?_⟩
  rintro ⟨X, _, d, hd, hG, hfree⟩
  obtain ⟨x⟩ := hd.nonempty
  exact ⟨hd.basedLength hG x, (hd.isFree_basedLength_iff hG x).2 hfree⟩

end TauCeti.LyndonLength
