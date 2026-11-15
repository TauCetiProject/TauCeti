/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map

/-!
# Retained-arrow chart atlases and their presenting groupoids

An orbifold chart `[U_i / G_i]` is presented by the action groupoid `G_i ⋉ U_i`, which keeps all
elements of `G_i` as distinct arrow labels even when they act trivially on `U_i`. Gluing a family of
such charts without erasing ineffective isotropy requires overlap data consisting of actual arrows
between charts rather than mere germs of diffeomorphisms: for each pair of indices `(i, j)`, an
overlap-arrow space `R i j` with source in `U i`, target in `U j`, associative composition with
units and inverses, and a postcomposition action of `G j` making every nonempty source fiber into a
`G j`-torsor.

`TauCeti.ChartAtlas` axiomatizes this algebraic structure for an arbitrary indexed family of group
actions `G i ↷ U i`. Because `G i` acts freely and transitively on each source fiber of the
diagonal `R i i`, postcomposing the unit section identifies `G i × U i` with `R i i`
(`TauCeti.ChartAtlas.diagEquiv`), retaining every ineffective label.

Assembling the charts on `Σ i, U i` and the overlap arrows on `Σ p : ι × ι, R p.1 p.2` produces the
presenting groupoid `𝓐.Obj`, into which each action groupoid `ActionCategory (G i) (U i)` embeds
fully and faithfully (`TauCeti.ChartAtlas.chartFunctor`). Consequently, the automorphism group of
`⟨i, x⟩` in `𝓐.Obj` is canonically isomorphic to `stabilizer (G i) x`
(`TauCeti.ChartAtlas.stabilizerMulEquivAutObj`), and each overlap arrow `α : R i j` conjugates
`stabilizer (G i) (src α)` isomorphically onto `stabilizer (G j) (tgt α)`
(`TauCeti.ChartAtlas.stabilizerConj`), compatibly with units, composition, and `G j`-translates.
Morphisms (`TauCeti.ChartAtlas.Hom`) and natural transformations (`TauCeti.ChartAtlas.NatTrans`)
between chart atlases induce functors and natural isomorphisms between their presenting groupoids.

## Main declarations

* `TauCeti.ChartAtlas`: retained-arrow chart atlas for a family of actions `G i ↷ U i`.
* `TauCeti.ChartAtlas.instTorsorSourceFiber`: nonempty source fibers of `R i j` are `G j`-torsors.
* `TauCeti.ChartAtlas.diagEquiv`: identification `G i × U i ≃ R i i` via `(g, x) ↦ g • unit i x`.
* `TauCeti.ChartAtlas.Obj`, `TauCeti.ChartAtlas.chartFunctor`: the presenting groupoid and its
  fully faithful chart inclusions.
* `TauCeti.ChartAtlas.stabilizerMulEquivAutObj`, `TauCeti.ChartAtlas.stabilizerConj`: isotropy
  identification and stabilizer conjugation along overlap arrows.
* `TauCeti.ChartAtlas.Hom`, `TauCeti.ChartAtlas.NatTrans`: morphisms and natural transformations of
  chart atlases, with induced functors and natural isomorphisms.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Sections 2.2–2.4.
* I. Moerdijk and D. A. Pronk, *Orbifolds, sheaves and groupoids*, K-Theory 12 (1997), 3–21.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

@[expose] public section

open CategoryTheory MulAction

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace TauCeti

/-- A **retained-arrow chart atlas** for a family of groups `G i` acting on chart domains `U i`,
with overlap-arrow types `R i j` carrying postcomposition actions of `G j`.

Composition is written in categorical order (`comp α β h` traverses `α` followed by `β`). On each
overlap `R i j`, the group `G j` acts freely and transitively by postcomposition on arrows sharing a
common source (`existsUnique_smul_eq`), retaining all stabilizer labels on `R i i`. -/
structure ChartAtlas {ι : Type u₁} (G : ι → Type u₂) [∀ i, Group (G i)]
    (U : ι → Type u₃) [∀ i, MulAction (G i) (U i)]
    (R : ι → ι → Type u₄) [∀ i j, MulAction (G j) (R i j)] where
  /-- The source point of an overlap arrow in the `i`-th chart. -/
  src : ∀ {i j}, R i j → U i
  /-- The target point of an overlap arrow in the `j`-th chart. -/
  tgt : ∀ {i j}, R i j → U j
  /-- The identity overlap arrow at a point of the `i`-th chart. -/
  unit : ∀ i, U i → R i i
  /-- The inverse of an overlap arrow. -/
  inv : ∀ {i j}, R i j → R j i
  /-- Categorical composition of composable overlap arrows: `α` followed by `β`. -/
  comp : ∀ {i j k} (α : R i j) (β : R j k), tgt α = src β → R i k
  /-- The source of a unit arrow is its base point. -/
  src_unit : ∀ (i : ι) (x : U i), src (unit i x) = x
  /-- The target of a unit arrow is its base point. -/
  tgt_unit : ∀ (i : ι) (x : U i), tgt (unit i x) = x
  /-- Inversion swaps target to source. -/
  src_inv : ∀ {i j} (α : R i j), src (inv α) = tgt α
  /-- Inversion swaps source to target. -/
  tgt_inv : ∀ {i j} (α : R i j), tgt (inv α) = src α
  /-- Composition takes its source from the first arrow. -/
  src_comp : ∀ {i j k} (α : R i j) (β : R j k) (h : tgt α = src β), src (comp α β h) = src α
  /-- Composition takes its target from the second arrow. -/
  tgt_comp : ∀ {i j k} (α : R i j) (β : R j k) (h : tgt α = src β), tgt (comp α β h) = tgt β
  /-- Left unit law for overlap-arrow composition. -/
  unit_comp : ∀ {i j} (x : U i) (α : R i j) (h : tgt (unit i x) = src α), comp (unit i x) α h = α
  /-- Right unit law for overlap-arrow composition. -/
  comp_unit : ∀ {i j} (α : R i j) (y : U j) (h : tgt α = src (unit j y)), comp α (unit j y) h = α
  /-- Associativity of overlap-arrow composition. -/
  comp_assoc : ∀ {i j k l} (α : R i j) (β : R j k) (γ : R k l)
    (h₁ : tgt α = src β) (h₂ : tgt β = src γ),
    comp (comp α β h₁) γ ((tgt_comp α β h₁).trans h₂) =
      comp α (comp β γ h₂) (h₁.trans (src_comp β γ h₂).symm)
  /-- Right inverse law for overlap arrows. -/
  comp_inv : ∀ {i j} (α : R i j), comp α (inv α) (src_inv α).symm = unit i (src α)
  /-- Left inverse law for overlap arrows. -/
  inv_comp : ∀ {i j} (α : R i j), comp (inv α) α (tgt_inv α) = unit j (tgt α)
  /-- Postcomposition by `G j` preserves the source in `U i`. -/
  src_smul : ∀ {i j} (g : G j) (α : R i j), src (g • α) = src α
  /-- Postcomposition by `G j` translates the target in `U j`. -/
  tgt_smul : ∀ {i j} (g : G j) (α : R i j), tgt (g • α) = g • tgt α
  /-- Postcomposition by `G k` commutes with composition on the left. -/
  comp_smul : ∀ {i j k} (α : R i j) (g : G k) (β : R j k) (h : tgt α = src β),
    comp α (g • β) (h.trans (src_smul g β).symm) = g • comp α β h
  /-- Two overlap arrows in `R i j` with the same source differ by a unique element of `G j`. -/
  existsUnique_smul_eq : ∀ {i j} (α β : R i j), src α = src β → ∃! g : G j, g • α = β

namespace ChartAtlas

section Basic

variable {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)]
  (𝓐 : ChartAtlas G U R)

attribute [simp] src_unit tgt_unit src_inv tgt_inv src_comp tgt_comp
  unit_comp comp_unit comp_inv inv_comp src_smul tgt_smul

/-- Composition of overlap arrows is independent of the composability proof. -/
theorem comp_congr {i j k : ι} {α α' : R i j} {β β' : R j k}
    (hα : α = α') (hβ : β = β') (h : 𝓐.tgt α = 𝓐.src β) (h' : 𝓐.tgt α' = 𝓐.src β') :
    𝓐.comp α β h = 𝓐.comp α' β' h' := by
  subst hα hβ
  rfl

/-- Two chart atlases on the same actions and overlap types are equal when their sources, targets,
and compositions agree; units and inverses are then uniquely determined. -/
@[ext]
theorem ext {𝓐 𝓑 : ChartAtlas G U R}
    (hsrc : ∀ {i j} (α : R i j), 𝓐.src α = 𝓑.src α)
    (htgt : ∀ {i j} (α : R i j), 𝓐.tgt α = 𝓑.tgt α)
    (hcomp : ∀ {i j k} (α : R i j) (β : R j k)
      (h₁ : 𝓐.tgt α = 𝓐.src β) (h₂ : 𝓑.tgt α = 𝓑.src β), 𝓐.comp α β h₁ = 𝓑.comp α β h₂) :
    𝓐 = 𝓑 := by
  have hunit : 𝓐.unit = 𝓑.unit := by
    funext i x
    have h₁ : 𝓐.tgt (𝓐.unit i x) = 𝓐.src (𝓑.unit i x) := by rw [hsrc]; simp
    have h₂ : 𝓑.tgt (𝓐.unit i x) = 𝓑.src (𝓑.unit i x) := by rw [← htgt]; simp
    exact (𝓑.comp_unit (𝓐.unit i x) x h₂).symm.trans
      ((hcomp _ _ h₁ h₂).symm.trans (𝓐.unit_comp x (𝓑.unit i x) h₁))
  have hinv : @𝓐.inv = @𝓑.inv := by
    funext i j α
    have h₁ : 𝓐.tgt (𝓐.inv α) = 𝓐.src α := 𝓐.tgt_inv α
    have h₂ : 𝓐.tgt α = 𝓐.src (𝓑.inv α) := by rw [htgt, hsrc]; simp
    have h₂' : 𝓑.tgt α = 𝓑.src (𝓑.inv α) := (𝓑.src_inv α).symm
    have h₃ : 𝓐.tgt (𝓐.inv α) = 𝓐.src (𝓐.comp α (𝓑.inv α) h₂) := by simp
    calc 𝓐.inv α
        = 𝓐.comp (𝓐.inv α) (𝓐.unit i (𝓐.src α)) (by simp) := by simp
      _ = 𝓐.comp (𝓐.inv α) (𝓐.comp α (𝓑.inv α) h₂) h₃ := by
          refine 𝓐.comp_congr rfl ?_ _ _
          rw [hcomp α (𝓑.inv α) h₂ h₂', 𝓑.comp_inv, ← hsrc, hunit]
      _ = 𝓐.comp (𝓐.comp (𝓐.inv α) α h₁) (𝓑.inv α) _ := (𝓐.comp_assoc _ _ _ _ _).symm
      _ = 𝓑.inv α := by simp
  cases 𝓐
  cases 𝓑
  have hs : _ = _ := funext fun i ↦ funext fun j ↦ funext (@hsrc i j)
  have ht : _ = _ := funext fun i ↦ funext fun j ↦ funext (@htgt i j)
  subst hs ht hunit hinv
  congr
  funext i j k α β h
  exact hcomp α β h h

/-- Inversion on overlap arrows is an involution. -/
@[simp]
theorem inv_inv {i j : ι} (α : R i j) : 𝓐.inv (𝓐.inv α) = α := by
  calc 𝓐.inv (𝓐.inv α)
      = 𝓐.comp (𝓐.inv (𝓐.inv α)) (𝓐.comp (𝓐.inv α) α (𝓐.tgt_inv α)) (by simp) := by simp
    _ = 𝓐.comp (𝓐.comp (𝓐.inv (𝓐.inv α)) (𝓐.inv α) (𝓐.tgt_inv _)) α _ :=
        (𝓐.comp_assoc _ _ _ _ _).symm
    _ = α := by simp

/-- Postcomposing a unit arrow by `g₂` and then by `g₁` gives the unit arrow translated by
`g₁ * g₂`. -/
@[simp]
theorem comp_smul_unit {i : ι} (g₁ g₂ : G i) (x : U i) (h) :
    𝓐.comp (g₂ • 𝓐.unit i x) (g₁ • 𝓐.unit i (g₂ • x)) h = (g₁ * g₂) • 𝓐.unit i x := by
  have h₀ : 𝓐.tgt (g₂ • 𝓐.unit i x) = 𝓐.src (𝓐.unit i (g₂ • x)) := by simp
  calc 𝓐.comp (g₂ • 𝓐.unit i x) (g₁ • 𝓐.unit i (g₂ • x)) h
      = 𝓐.comp (g₂ • 𝓐.unit i x) (g₁ • 𝓐.unit i (g₂ • x))
          (h₀.trans (𝓐.src_smul g₁ _).symm) := rfl
    _ = g₁ • 𝓐.comp (g₂ • 𝓐.unit i x) (𝓐.unit i (g₂ • x)) h₀ := 𝓐.comp_smul _ _ _ h₀
    _ = (g₁ * g₂) • 𝓐.unit i x := by simp [mul_smul]

/-- Postcomposing an arrow `α` by `g` is composing `α` with the `g`-translated unit at `tgt α`. -/
theorem comp_smul_unit_tgt {i j : ι} (α : R i j) (g : G j) (h) :
    𝓐.comp α (g • 𝓐.unit j (𝓐.tgt α)) h = g • α := by
  have h₀ : 𝓐.tgt α = 𝓐.src (𝓐.unit j (𝓐.tgt α)) := by simp
  exact (𝓐.comp_smul α g (𝓐.unit j (𝓐.tgt α)) h₀).trans (by simp)

/-- Inverting a `g`-translated unit arrow gives the `g⁻¹`-translated unit at `g • x`. -/
@[simp]
theorem inv_smul_unit {i : ι} (g : G i) (x : U i) :
    𝓐.inv (g • 𝓐.unit i x) = g⁻¹ • 𝓐.unit i (g • x) := by
  calc 𝓐.inv (g • 𝓐.unit i x)
      = 𝓐.comp (𝓐.inv (g • 𝓐.unit i x)) (𝓐.unit i x) (by simp) := by simp
    _ = 𝓐.comp (𝓐.inv (g • 𝓐.unit i x))
          (𝓐.comp (g • 𝓐.unit i x) (g⁻¹ • 𝓐.unit i (g • x)) (by simp)) (by simp) :=
        𝓐.comp_congr rfl (by simp) _ _
    _ = 𝓐.comp (𝓐.comp (𝓐.inv (g • 𝓐.unit i x)) (g • 𝓐.unit i x) (by simp))
          (g⁻¹ • 𝓐.unit i (g • x)) _ := (𝓐.comp_assoc _ _ _ _ _).symm
    _ = g⁻¹ • 𝓐.unit i (g • x) := by simp

end Basic

section Torsor

variable {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)]
  (𝓐 : ChartAtlas G U R)

/-- The fiber of overlap arrows in `R i j` over a fixed source point `x : U i`. -/
abbrev SourceFiber {i : ι} (j : ι) (x : U i) : Type u₄ :=
  { α : R i j // 𝓐.src α = x }

/-- `G j` acts by postcomposition on each source fiber of `R i j`. -/
instance instMulActionSourceFiber {i : ι} (j : ι) (x : U i) :
    MulAction (G j) (𝓐.SourceFiber j x) where
  smul g α := ⟨g • α.1, (𝓐.src_smul g α.1).trans α.2⟩
  one_smul α := Subtype.ext (one_smul _ α.1)
  mul_smul g₁ g₂ α := Subtype.ext (mul_smul g₁ g₂ α.1)

/-- Coercion from a source fiber commutes with the `G j`-action. -/
@[simp]
theorem val_smul_sourceFiber {i j : ι} {x : U i} (g : G j) (α : 𝓐.SourceFiber j x) :
    (g • α).1 = g • α.1 := (rfl)

/-- The unique element of `G j` carrying `β` to `α` in a common source fiber. -/
noncomputable instance instSDivSourceFiber {i : ι} (j : ι) (x : U i) :
    SDiv (G j) (𝓐.SourceFiber j x) where
  sdiv α β := (𝓐.existsUnique_smul_eq β.1 α.1 (β.2.trans α.2.symm)).choose

/-- Applying `α /ₛ β` to `β` in a source fiber recovers `α`. -/
@[simp]
theorem sdiv_smul_sourceFiber {i j : ι} {x : U i} (α β : 𝓐.SourceFiber j x) :
    (α /ₛ β) • β = α :=
  Subtype.ext (𝓐.existsUnique_smul_eq β.1 α.1 (β.2.trans α.2.symm)).choose_spec.1

/-- **Overlap-arrow torsor.** Every nonempty source fiber of `R i j` is a `G j`-torsor under
postcomposition. -/
noncomputable instance instTorsorSourceFiber {i : ι} (j : ι) (x : U i)
    [Nonempty (𝓐.SourceFiber j x)] : Torsor (G j) (𝓐.SourceFiber j x) where
  sdiv_smul' := 𝓐.sdiv_smul_sourceFiber
  smul_sdiv' g α :=
    let h := 𝓐.existsUnique_smul_eq α.1 (g • α.1) (𝓐.src_smul g α.1).symm
    h.unique h.choose_spec.1 rfl

/-- On the diagonal `R i i`, postcomposing the unit arrow identifies `G i × U i` with `R i i`,
retaining every element of `G i` even when it acts trivially on `U i`. -/
noncomputable def diagEquiv (i : ι) : G i × U i ≃ R i i where
  toFun p := p.1 • 𝓐.unit i p.2
  invFun α := ((𝓐.existsUnique_smul_eq (𝓐.unit i (𝓐.src α)) α (𝓐.src_unit i _)).choose, 𝓐.src α)
  left_inv p := by
    have hsrc : 𝓐.src (p.1 • 𝓐.unit i p.2) = p.2 := by simp
    refine Prod.ext ?_ hsrc
    have h := 𝓐.existsUnique_smul_eq (𝓐.unit i (𝓐.src (p.1 • 𝓐.unit i p.2)))
      (p.1 • 𝓐.unit i p.2) (𝓐.src_unit i _)
    exact h.unique h.choose_spec.1 (by rw [hsrc])
  right_inv α := (𝓐.existsUnique_smul_eq (𝓐.unit i (𝓐.src α)) α (𝓐.src_unit i _)).choose_spec.1

/-- `diagEquiv i` translates the unit at `p.2` by `p.1`. -/
@[simp]
theorem diagEquiv_apply (i : ι) (p : G i × U i) :
    𝓐.diagEquiv i p = p.1 • 𝓐.unit i p.2 := (rfl)

/-- The source of `diagEquiv i (g, x)` is `x`. -/
theorem src_diagEquiv (i : ι) (p : G i × U i) :
    𝓐.src (𝓐.diagEquiv i p) = p.2 := by simp

/-- The target of `diagEquiv i (g, x)` is `g • x`. -/
theorem tgt_diagEquiv (i : ι) (p : G i × U i) :
    𝓐.tgt (𝓐.diagEquiv i p) = p.1 • p.2 := by simp

/-- The second coordinate of `(diagEquiv i).symm α` is `src α`. -/
@[simp]
theorem snd_diagEquiv_symm (i : ι) (α : R i i) :
    ((𝓐.diagEquiv i).symm α).2 = 𝓐.src α := (rfl)

end Torsor

section PresentingGroupoid

variable {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)]

/-- An object of the presenting groupoid of a chart atlas `𝓐`: a chart index `chart : ι` together
with a point `point : U chart`. -/
@[ext]
structure Obj (𝓐 : ChartAtlas G U R) where
  /-- The chart index of the object. -/
  chart : ι
  /-- The point in `U chart` underlying the object. -/
  point : U chart

variable (𝓐 : ChartAtlas G U R)

/-- Equivalence between objects of `𝓐.Obj` and the disjoint union `Σ i, U i` of the chart domains.
-/
def objEquiv : 𝓐.Obj ≃ Σ i, U i where
  toFun x := ⟨x.chart, x.point⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `objEquiv` records the chart index and point of an object. -/
@[simp]
theorem objEquiv_apply (x : 𝓐.Obj) : 𝓐.objEquiv x = ⟨x.chart, x.point⟩ := (rfl)

/-- `objEquiv.symm` constructs an object from a chart index and point. -/
@[simp]
theorem objEquiv_symm_apply (p : Σ i, U i) : 𝓐.objEquiv.symm p = ⟨p.1, p.2⟩ := (rfl)

/-- A morphism in the presenting groupoid of `𝓐` from `x` to `y`: an overlap arrow in
`R x.chart y.chart` with source `x.point` and target `y.point`. -/
@[ext]
structure Obj.Hom {𝓐 : ChartAtlas G U R} (x y : 𝓐.Obj) where
  /-- The underlying overlap arrow. -/
  arrow : R x.chart y.chart
  /-- Source compatibility of the overlap arrow. -/
  src_arrow : 𝓐.src arrow = x.point
  /-- Target compatibility of the overlap arrow. -/
  tgt_arrow : 𝓐.tgt arrow = y.point

/-- The presenting groupoid structure on `𝓐.Obj`. -/
instance instGroupoidObj : Groupoid 𝓐.Obj where
  Hom := Obj.Hom
  id x := ⟨𝓐.unit x.chart x.point, 𝓐.src_unit _ _, 𝓐.tgt_unit _ _⟩
  comp f g := ⟨𝓐.comp f.arrow g.arrow (f.tgt_arrow.trans g.src_arrow.symm),
    (𝓐.src_comp _ _ _).trans f.src_arrow, (𝓐.tgt_comp _ _ _).trans g.tgt_arrow⟩
  inv f := ⟨𝓐.inv f.arrow, (𝓐.src_inv _).trans f.tgt_arrow, (𝓐.tgt_inv _).trans f.src_arrow⟩
  id_comp _ := Obj.Hom.ext (𝓐.unit_comp _ _ _)
  comp_id _ := Obj.Hom.ext (𝓐.comp_unit _ _ _)
  assoc _ _ _ := Obj.Hom.ext (𝓐.comp_assoc _ _ _ _ _)
  inv_comp f := Obj.Hom.ext ((𝓐.inv_comp _).trans (congrArg (𝓐.unit _) f.tgt_arrow))
  comp_inv f := Obj.Hom.ext ((𝓐.comp_inv _).trans (congrArg (𝓐.unit _) f.src_arrow))

/-- The underlying overlap arrow of the identity morphism at `x`. -/
@[simp]
theorem id_arrow (x : 𝓐.Obj) : (𝟙 x : x ⟶ x).arrow = 𝓐.unit x.chart x.point := (rfl)

/-- The underlying overlap arrow of a composite morphism in `𝓐.Obj`. -/
@[simp]
theorem comp_arrow {x y z : 𝓐.Obj} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).arrow = 𝓐.comp f.arrow g.arrow (f.tgt_arrow.trans g.src_arrow.symm) := (rfl)

/-- The underlying overlap arrow of a categorical inverse in `𝓐.Obj`. -/
@[simp]
theorem inv_arrow {x y : 𝓐.Obj} (f : x ⟶ y) :
    (CategoryTheory.inv f).arrow = 𝓐.inv f.arrow := by
  rw [← Groupoid.inv_eq_inv]
  rfl

/-- An `eqToHom` morphism in `𝓐.Obj` has the unit overlap arrow at its source. -/
@[simp]
theorem eqToHom_arrow {x y : 𝓐.Obj} (h : x = y) :
    (eqToHom h).arrow = h ▸ 𝓐.unit x.chart x.point := by
  subst h
  rfl

/-- An `eqToHom` morphism within the same chart `i` has underlying arrow `unit i x`. -/
theorem eqToHom_mk_arrow {i : ι} {x y : U i} (h : (⟨i, x⟩ : 𝓐.Obj) = ⟨i, y⟩) :
    (eqToHom h).arrow = 𝓐.unit i x := by
  cases h
  rfl

/-- Equivalence between the total arrows of `𝓐.Obj` and the disjoint union
`Σ p : ι × ι, R p.1 p.2` of all overlap-arrow types. -/
def totalEquiv : Quiver.Total 𝓐.Obj ≃ Σ p : ι × ι, R p.1 p.2 where
  toFun a := ⟨(a.left.chart, a.right.chart), a.hom.arrow⟩
  invFun q := ⟨⟨q.1.1, 𝓐.src q.2⟩, ⟨q.1.2, 𝓐.tgt q.2⟩, ⟨q.2, rfl, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨i, x⟩, ⟨j, y⟩, ⟨α, hs, ht⟩⟩
    have key : ∀ (x' : U i) (y' : U j) (f' : (⟨i, x'⟩ : 𝓐.Obj) ⟶ ⟨j, y'⟩),
        x' = x → y' = y → f'.arrow = α →
        (⟨⟨i, x'⟩, ⟨j, y'⟩, f'⟩ : Quiver.Total 𝓐.Obj) = ⟨⟨i, x⟩, ⟨j, y⟩, ⟨α, hs, ht⟩⟩ := by
      rintro _ _ f' rfl rfl h
      exact congrArg _ (Obj.Hom.ext h)
    exact key _ _ _ hs ht rfl
  right_inv _ := rfl

/-- `totalEquiv` sends a total arrow to its pair of chart indices and underlying overlap arrow. -/
@[simp]
theorem totalEquiv_apply (a : Quiver.Total 𝓐.Obj) :
    𝓐.totalEquiv a = ⟨(a.left.chart, a.right.chart), a.hom.arrow⟩ := (rfl)

/-- The source of `totalEquiv.symm ⟨(i, j), α⟩` is `⟨i, src α⟩`. -/
@[simp]
theorem totalEquiv_symm_left (p : Σ q : ι × ι, R q.1 q.2) :
    (𝓐.totalEquiv.symm p).left = ⟨p.1.1, 𝓐.src p.2⟩ := (rfl)

/-- The target of `totalEquiv.symm ⟨(i, j), α⟩` is `⟨j, tgt α⟩`. -/
@[simp]
theorem totalEquiv_symm_right (p : Σ q : ι × ι, R q.1 q.2) :
    (𝓐.totalEquiv.symm p).right = ⟨p.1.2, 𝓐.tgt p.2⟩ := (rfl)

/-- The underlying overlap arrow of `totalEquiv.symm ⟨(i, j), α⟩` is `α`. -/
@[simp]
theorem totalEquiv_symm_hom_arrow (p : Σ q : ι × ι, R q.1 q.2) :
    (𝓐.totalEquiv.symm p).hom.arrow = p.2 := (rfl)

/-- The canonical inclusion functor `ActionCategory (G i) (U i) ⥤ 𝓐.Obj` of the `i`-th chart into
the presenting groupoid, retaining all group labels. -/
def chartFunctor (i : ι) : ActionCategory (G i) (U i) ⥤ 𝓐.Obj where
  obj a := ⟨i, a.back⟩
  map {a _} f := ⟨f.hom • 𝓐.unit i a.back, (𝓐.src_smul _ _).trans (𝓐.src_unit _ _),
    (𝓐.tgt_smul _ _).trans ((congrArg (f.hom • ·) (𝓐.tgt_unit _ _)).trans f.map_val)⟩
  map_id a := Obj.Hom.ext (one_smul (G i) (𝓐.unit i a.back))
  map_comp {a b _} f g := Obj.Hom.ext <| by
    have hf : f.hom • a.back = b.back := ActionCategory.hom_smul f
    refine (congrArg (· • 𝓐.unit i a.back) (ActionCategory.comp_hom f g)).trans ?_
    exact (𝓐.comp_smul_unit g.hom f.hom a.back (by simp)).symm.trans
      (𝓐.comp_congr rfl (congrArg (g.hom • 𝓐.unit i ·) hf) _ _)

/-- `chartFunctor i` sends an object `a` of the action category to `⟨i, a.back⟩`. -/
@[simp]
theorem chartFunctor_obj (i : ι) (a : ActionCategory (G i) (U i)) :
    (𝓐.chartFunctor i).obj a = ⟨i, a.back⟩ := (rfl)

/-- `chartFunctor i` maps an arrow labelled `g` at `a` to `g • unit i a.back`. -/
@[simp]
theorem chartFunctor_map_arrow (i : ι) {a b : ActionCategory (G i) (U i)} (f : a ⟶ b) :
    ((𝓐.chartFunctor i).map f).arrow = f.hom • 𝓐.unit i a.back := (rfl)

/-- Each chart inclusion `chartFunctor i` is faithful, keeping every group label distinct. -/
instance instFaithfulChartFunctor (i : ι) : (𝓐.chartFunctor i).Faithful where
  map_injective {a _} _ f₂ h := Functor.Elements.hom_ext <|
    (𝓐.existsUnique_smul_eq (𝓐.unit i a.back) (f₂.hom • 𝓐.unit i a.back)
      (𝓐.src_smul _ _).symm).unique (congrArg Obj.Hom.arrow h) rfl

/-- Each chart inclusion `chartFunctor i` is full: every overlap arrow in `R i i` comes from `G i`.
-/
instance instFullChartFunctor (i : ι) : (𝓐.chartFunctor i).Full where
  map_surjective {a b} m := by
    obtain ⟨g, hg, -⟩ :=
      𝓐.existsUnique_smul_eq (𝓐.unit i a.back) m.arrow ((𝓐.src_unit i _).trans m.src_arrow.symm)
    have hgx : g • a.back = b.back := by
      calc g • a.back = g • 𝓐.tgt (𝓐.unit i a.back) := by simp
        _ = 𝓐.tgt (g • 𝓐.unit i a.back) := (𝓐.tgt_smul _ _).symm
        _ = b.back := hg ▸ m.tgt_arrow
    exact ⟨Functor.Elements.homMk g hgx, Obj.Hom.ext hg⟩

/-- In total-arrow coordinates, `chartFunctor i` acts as `diagEquiv i` followed by the `(i, i)`
component inclusion. -/
theorem totalEquiv_mapTotal_chartFunctor (i : ι) (p : G i × U i) :
    𝓐.totalEquiv ((𝓐.chartFunctor i).toPrefunctor.mapTotal
      ((ActionCategory.totalEquiv (G i) (U i)).symm p)) =
      ⟨(i, i), 𝓐.diagEquiv i p⟩ := by
  simp [Prefunctor.mapTotal, diagEquiv]
  rfl

end PresentingGroupoid

section Isotropy

variable {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)]
  (𝓐 : ChartAtlas G U R)

/-- Loop in `R i i` formed by translating the unit at `x` by `h : stabilizer (G i) x` has target
`x`. -/
theorem tgt_smul_unit_of_stabilizer {i : ι} {x : U i} (h : stabilizer (G i) x) :
    𝓐.tgt ((h : G i) • 𝓐.unit i x) = x :=
  (𝓐.tgt_smul _ _).trans ((congrArg _ (𝓐.tgt_unit _ _)).trans h.2)

/-- The stabilizer `stabilizer (G i) x` is canonically isomorphic to the automorphism group of
`⟨i, x⟩` in the presenting groupoid `𝓐.Obj`, retaining all ineffective elements. -/
noncomputable def stabilizerMulEquivAutObj (i : ι) (x : U i) :
    stabilizer (G i) x ≃* Aut (⟨i, x⟩ : 𝓐.Obj) :=
  (ActionCategory.stabilizerMulEquivAut (G i) x).trans
    ((Functor.FullyFaithful.ofFullyFaithful (𝓐.chartFunctor i)).autMulEquivOfFullyFaithful
      (ActionCategory.objEquiv (G i) (U i) x))

/-- Forward arrow of `stabilizerMulEquivAutObj i x h` in `R i i`. -/
@[simp]
theorem stabilizerMulEquivAutObj_hom_arrow (i : ι) (x : U i) (h : stabilizer (G i) x) :
    (𝓐.stabilizerMulEquivAutObj i x h).asIso.hom.arrow = (h : G i) • 𝓐.unit i x := by
  change (((Functor.FullyFaithful.ofFullyFaithful (𝓐.chartFunctor i)).autMulEquivOfFullyFaithful
    (ActionCategory.objEquiv (G i) (U i) x))
      (ActionCategory.stabilizerMulEquivAut (G i) x h)).asIso.hom.arrow = _
  simp
  rfl

/-- **Stabilizer conjugation.** An overlap arrow `α : R i j` conjugates `stabilizer (G i) (src α)`
isomorphically onto `stabilizer (G j) (tgt α)`, retaining all ineffective elements. -/
noncomputable def stabilizerConj {i j : ι} (α : R i j) :
    stabilizer (G i) (𝓐.src α) ≃* stabilizer (G j) (𝓐.tgt α) :=
  (𝓐.stabilizerMulEquivAutObj i (𝓐.src α)).trans <|
    (Aut.autMulEquivOfIso
      ((Groupoid.isoEquivHom (⟨i, 𝓐.src α⟩ : 𝓐.Obj) ⟨j, 𝓐.tgt α⟩).symm ⟨α, rfl, rfl⟩)).trans
      (𝓐.stabilizerMulEquivAutObj j (𝓐.tgt α)).symm

/-- Defining intertwining equation of `stabilizerConj`: postcomposing `α` by `stabilizerConj α h`
equals precomposing `α` with the `h`-loop at `src α`. -/
theorem stabilizerConj_smul {i j : ι} (α : R i j) (h : stabilizer (G i) (𝓐.src α)) :
    (𝓐.stabilizerConj α h : G j) • α =
      𝓐.comp ((h : G i) • 𝓐.unit i (𝓐.src α)) α (𝓐.tgt_smul_unit_of_stabilizer h) := by
  set g := 𝓐.stabilizerConj α h
  have haut : 𝓐.stabilizerMulEquivAutObj j (𝓐.tgt α) g =
      Aut.autMulEquivOfIso ((Groupoid.isoEquivHom (⟨i, 𝓐.src α⟩ : 𝓐.Obj) ⟨j, 𝓐.tgt α⟩).symm
        ⟨α, rfl, rfl⟩) (𝓐.stabilizerMulEquivAutObj i (𝓐.src α) h) := by
    simp [g, stabilizerConj]
  let f : (⟨i, 𝓐.src α⟩ : 𝓐.Obj) ⟶ ⟨j, 𝓐.tgt α⟩ := ⟨α, rfl, rfl⟩
  have hmor : f ≫ (𝓐.stabilizerMulEquivAutObj j (𝓐.tgt α) g).asIso.hom =
      (𝓐.stabilizerMulEquivAutObj i (𝓐.src α) h).asIso.hom ≫ f := by
    rw [haut]
    simp [f, Aut.autMulEquivOfIso]
  simpa [f, 𝓐.comp_smul_unit_tgt] using congrArg Obj.Hom.arrow hmor

/-- Characterization of `stabilizerConj α h` by its postcomposition action on `α`. -/
theorem stabilizerConj_eq_iff {i j : ι} (α : R i j) (h : stabilizer (G i) (𝓐.src α))
    (g : stabilizer (G j) (𝓐.tgt α)) :
    𝓐.stabilizerConj α h = g ↔
      (g : G j) • α =
        𝓐.comp ((h : G i) • 𝓐.unit i (𝓐.src α)) α (𝓐.tgt_smul_unit_of_stabilizer h) := by
  constructor
  · rintro rfl
    exact 𝓐.stabilizerConj_smul α h
  · intro hg
    ext1
    exact (𝓐.existsUnique_smul_eq α _ (by simp)).unique (𝓐.stabilizerConj_smul α h) hg

/-- Stabilizer conjugation along a unit arrow is the identity on stabilizers. -/
@[simp]
theorem coe_stabilizerConj_unit (i : ι) (x : U i)
    (h : stabilizer (G i) (𝓐.src (𝓐.unit i x))) :
    (𝓐.stabilizerConj (𝓐.unit i x) h : G i) = h := by
  have heq : 𝓐.stabilizerConj (𝓐.unit i x) h = ⟨h, by simpa using h.2⟩ := by
    rw [𝓐.stabilizerConj_eq_iff]
    simp
  exact congrArg Subtype.val heq

/-- Stabilizer conjugation along a composite arrow is the composite of the stabilizer conjugations.
-/
theorem coe_stabilizerConj_comp {i j k : ι} (α : R i j) (β : R j k) (hab : 𝓐.tgt α = 𝓐.src β)
    (h : stabilizer (G i) (𝓐.src (𝓐.comp α β hab))) :
    (𝓐.stabilizerConj (𝓐.comp α β hab) h : G k) =
      𝓐.stabilizerConj β ⟨𝓐.stabilizerConj α ⟨h, by simpa using h.2⟩,
        by rw [mem_stabilizer_iff, ← hab]; exact (𝓐.stabilizerConj α _).2⟩ := by
  set h' : stabilizer (G i) (𝓐.src α) := ⟨h, by simpa using h.2⟩
  set u := 𝓐.stabilizerConj α h'
  set u' : stabilizer (G j) (𝓐.src β) := ⟨u, hab ▸ u.2⟩
  set v := 𝓐.stabilizerConj β u'
  have hu_tgt : 𝓐.tgt ((u : G j) • α) = 𝓐.src β :=
    (𝓐.tgt_smul _ _).trans ((mem_stabilizer_iff.mp u.2).trans hab)
  have hv : 𝓐.stabilizerConj (𝓐.comp α β hab) h = ⟨v, by simp⟩ := by
    rw [𝓐.stabilizerConj_eq_iff]
    calc (v : G k) • 𝓐.comp α β hab
        = 𝓐.comp α ((v : G k) • β) (hab.trans (𝓐.src_smul _ β).symm) := (𝓐.comp_smul _ _ _ _).symm
      _ = 𝓐.comp α (𝓐.comp ((u : G j) • 𝓐.unit j (𝓐.src β)) β (𝓐.tgt_smul_unit_of_stabilizer u'))
            (by simpa using hab) := 𝓐.comp_congr rfl (𝓐.stabilizerConj_smul β u') _ _
      _ = 𝓐.comp (𝓐.comp α ((u : G j) • 𝓐.unit j (𝓐.tgt α)) (by simp)) β
            (by simpa using hu_tgt) :=
          (𝓐.comp_assoc _ _ _ (by simpa using hab) _).symm.trans
            (𝓐.comp_congr (𝓐.comp_congr rfl
              (congrArg ((u : G j) • 𝓐.unit j ·) hab.symm) _ _) rfl _ _)
      _ = 𝓐.comp ((u : G j) • α) β hu_tgt :=
          𝓐.comp_congr (𝓐.comp_smul_unit_tgt α u _) rfl _ _
      _ = 𝓐.comp (𝓐.comp ((h : G i) • 𝓐.unit i (𝓐.src α)) α (𝓐.tgt_smul_unit_of_stabilizer h')) β
            (by simpa using hab) := 𝓐.comp_congr (𝓐.stabilizerConj_smul α h') rfl _ _
      _ = 𝓐.comp ((h : G i) • 𝓐.unit i (𝓐.src (𝓐.comp α β hab))) (𝓐.comp α β hab)
            (𝓐.tgt_smul_unit_of_stabilizer h) :=
          (𝓐.comp_assoc _ _ _ _ hab).trans (𝓐.comp_congr (by simp) rfl _ _)
  exact congrArg Subtype.val hv

/-- Translating an overlap arrow `α` by `g : G j` conjugates `stabilizerConj α` by `g`. -/
theorem coe_stabilizerConj_smul_arrow {i j : ι} (g : G j) (α : R i j)
    (h : stabilizer (G i) (𝓐.src (g • α))) :
    (𝓐.stabilizerConj (g • α) h : G j) =
      stabilizerEquivStabilizer (𝓐.tgt_smul g α)
        (𝓐.stabilizerConj α ⟨h, by simpa using h.2⟩) := by
  set h' : stabilizer (G i) (𝓐.src α) := ⟨h, by simpa using h.2⟩
  set u := 𝓐.stabilizerConj α h'
  set w := stabilizerEquivStabilizer (𝓐.tgt_smul g α) u
  have hw : 𝓐.stabilizerConj (g • α) h = w := by
    rw [𝓐.stabilizerConj_eq_iff]
    have hconj : (w : G j) = g * (u : G j) * g⁻¹ := by
      simp [w, stabilizerEquivStabilizer_apply, MulAut.conj_apply]
    calc (w : G j) • (g • α)
        = (g * (u : G j)) • α := by rw [hconj, smul_smul, inv_mul_cancel_right]
      _ = g • ((u : G j) • α) := mul_smul g u α
      _ = g • 𝓐.comp ((h' : G i) • 𝓐.unit i (𝓐.src α)) α (𝓐.tgt_smul_unit_of_stabilizer h') := by
          rw [𝓐.stabilizerConj_smul α h']
      _ = 𝓐.comp ((h : G i) • 𝓐.unit i (𝓐.src (g • α))) (g • α)
            (𝓐.tgt_smul_unit_of_stabilizer h) := by
          rw [← 𝓐.comp_smul]
          exact 𝓐.comp_congr (by simp [h']) rfl _ _
  exact congrArg Subtype.val hw

end Isotropy

section HomAndNatTrans

variable {ι : Type u₁} {G : ι → Type u₂} [∀ i, Group (G i)]
  {U : ι → Type u₃} [∀ i, MulAction (G i) (U i)]
  {R : ι → ι → Type u₄} [∀ i j, MulAction (G j) (R i j)]
  {κ : Type v₁} {G' : κ → Type v₂} [∀ k, Group (G' k)]
  {U' : κ → Type v₃} [∀ k, MulAction (G' k) (U' k)]
  {R' : κ → κ → Type v₄} [∀ k l, MulAction (G' l) (R' k l)]

/-- A morphism (refinement map) between retained-arrow chart atlases `𝓐` and `𝓑`: a chart
reindexing `index`, group homomorphisms `groupHom i : G i →* G' (index i)`, chart maps
`obj i : U i → U' (index i)`, and overlap-arrow maps `map : R i j → R' (index i) (index j)`
preserving sources, targets, units, composition, and postcomposition actions. -/
structure Hom (𝓐 : ChartAtlas G U R) (𝓑 : ChartAtlas G' U' R') where
  /-- Reindexing map on charts. -/
  index : ι → κ
  /-- Group homomorphisms on chart groups. -/
  groupHom : ∀ i, G i →* G' (index i)
  /-- Point maps on chart domains. -/
  obj : ∀ i, U i → U' (index i)
  /-- Maps on overlap-arrow types. -/
  map : ∀ {i j}, R i j → R' (index i) (index j)
  /-- Source compatibility of `map`. -/
  src_map : ∀ {i j} (α : R i j), 𝓑.src (map α) = obj i (𝓐.src α)
  /-- Target compatibility of `map`. -/
  tgt_map : ∀ {i j} (α : R i j), 𝓑.tgt (map α) = obj j (𝓐.tgt α)
  /-- Preservation of unit overlap arrows. -/
  map_unit : ∀ i (x : U i), map (𝓐.unit i x) = 𝓑.unit (index i) (obj i x)
  /-- Preservation of overlap-arrow composition. -/
  map_comp : ∀ {i j k} (α : R i j) (β : R j k) (h : 𝓐.tgt α = 𝓐.src β),
    map (𝓐.comp α β h) = 𝓑.comp (map α) (map β)
      ((tgt_map α).trans ((congrArg (obj j) h).trans (src_map β).symm))
  /-- Equivariance of `map` with respect to `groupHom`. -/
  map_smul : ∀ {i j} (g : G j) (α : R i j), map (g • α) = groupHom j g • map α

namespace Hom

variable {𝓐 : ChartAtlas G U R} {𝓑 : ChartAtlas G' U' R'}

attribute [simp] src_map tgt_map map_unit map_smul

/-- Extensionality for morphisms of chart atlases. -/
@[ext]
theorem ext {Φ Ψ : 𝓐.Hom 𝓑} (hindex : Φ.index = Ψ.index)
    (hgroup : ∀ i, HEq (Φ.groupHom i) (Ψ.groupHom i))
    (hobj : ∀ i, HEq (Φ.obj i) (Ψ.obj i))
    (hmap : ∀ {i j} (α : R i j), HEq (Φ.map α) (Ψ.map α)) : Φ = Ψ := by
  obtain ⟨idx₁, grp₁, obj₁, map₁, _, _, _, _, _⟩ := Φ
  obtain ⟨idx₂, grp₂, obj₂, map₂, _, _, _, _, _⟩ := Ψ
  dsimp only at hindex hgroup hobj hmap
  subst hindex
  have hg : grp₁ = grp₂ := funext fun i ↦ eq_of_heq (hgroup i)
  have ho : obj₁ = obj₂ := funext fun i ↦ eq_of_heq (hobj i)
  have hm : @map₁ = @map₂ := funext fun i ↦ funext fun j ↦ funext fun α ↦ eq_of_heq (hmap α)
  subst hg ho hm
  rfl

/-- Each chart map `Φ.obj i` is automatically `Φ.groupHom i`-equivariant. -/
@[simp]
theorem obj_smul (Φ : 𝓐.Hom 𝓑) (i : ι) (g : G i) (x : U i) :
    Φ.obj i (g • x) = Φ.groupHom i g • Φ.obj i x := by
  calc Φ.obj i (g • x)
      = Φ.obj i (𝓐.tgt (g • 𝓐.unit i x)) := by simp
    _ = 𝓑.tgt (Φ.map (g • 𝓐.unit i x)) := (Φ.tgt_map _).symm
    _ = Φ.groupHom i g • Φ.obj i x := by simp

/-- An atlas morphism preserves inverses of overlap arrows. -/
@[simp]
theorem map_inv (Φ : 𝓐.Hom 𝓑) {i j : ι} (α : R i j) :
    Φ.map (𝓐.inv α) = 𝓑.inv (Φ.map α) := by
  calc Φ.map (𝓐.inv α)
      = 𝓑.comp (Φ.map (𝓐.inv α)) (𝓑.unit (Φ.index i) (Φ.obj i (𝓐.src α))) (by simp) := by simp
    _ = 𝓑.comp (Φ.map (𝓐.inv α)) (𝓑.comp (Φ.map α) (𝓑.inv (Φ.map α)) (by simp)) (by simp) :=
        𝓑.comp_congr rfl (by simp) _ _
    _ = 𝓑.comp (𝓑.comp (Φ.map (𝓐.inv α)) (Φ.map α) (by simp)) (𝓑.inv (Φ.map α)) _ :=
        (𝓑.comp_assoc _ _ _ _ _).symm
    _ = 𝓑.comp (Φ.map (𝓐.comp (𝓐.inv α) α (𝓐.tgt_inv α))) (𝓑.inv (Φ.map α)) (by simp) :=
        𝓑.comp_congr (Φ.map_comp _ _ _).symm rfl _ _
    _ = 𝓑.inv (Φ.map α) := by simp

/-- The identity morphism on a chart atlas `𝓐`. -/
def id (𝓐 : ChartAtlas G U R) : 𝓐.Hom 𝓐 where
  index := _root_.id
  groupHom i := MonoidHom.id (G i)
  obj _ := _root_.id
  map α := α
  src_map _ := rfl
  tgt_map _ := rfl
  map_unit _ _ := rfl
  map_comp _ _ _ := rfl
  map_smul _ _ := rfl

/-- Composition of morphisms of chart atlases. -/
def comp {μ : Type*} {G'' : μ → Type*} [∀ m, Group (G'' m)]
    {U'' : μ → Type*} [∀ m, MulAction (G'' m) (U'' m)]
    {R'' : μ → μ → Type*} [∀ m n, MulAction (G'' n) (R'' m n)]
    {𝓒 : ChartAtlas G'' U'' R''} (Ψ : 𝓑.Hom 𝓒) (Φ : 𝓐.Hom 𝓑) : 𝓐.Hom 𝓒 where
  index := Ψ.index ∘ Φ.index
  groupHom i := (Ψ.groupHom (Φ.index i)).comp (Φ.groupHom i)
  obj i := Ψ.obj (Φ.index i) ∘ Φ.obj i
  map α := Ψ.map (Φ.map α)
  src_map α := (Ψ.src_map _).trans (congrArg (Ψ.obj _) (Φ.src_map α))
  tgt_map α := (Ψ.tgt_map _).trans (congrArg (Ψ.obj _) (Φ.tgt_map α))
  map_unit i x := (congrArg Ψ.map (Φ.map_unit i x)).trans (Ψ.map_unit _ _)
  map_comp α β h := (congrArg Ψ.map (Φ.map_comp α β h)).trans (Ψ.map_comp _ _ _)
  map_smul g α := (congrArg Ψ.map (Φ.map_smul g α)).trans (Ψ.map_smul _ _)

/-- The functor `𝓐.Obj ⥤ 𝓑.Obj` between presenting groupoids induced by an atlas morphism `Φ`. -/
def toFunctor (Φ : 𝓐.Hom 𝓑) : 𝓐.Obj ⥤ 𝓑.Obj where
  obj x := ⟨Φ.index x.chart, Φ.obj x.chart x.point⟩
  map f := ⟨Φ.map f.arrow, (Φ.src_map _).trans (congrArg _ f.src_arrow),
    (Φ.tgt_map _).trans (congrArg _ f.tgt_arrow)⟩
  map_id x := Obj.Hom.ext (Φ.map_unit x.chart x.point)
  map_comp f g := Obj.Hom.ext (Φ.map_comp f.arrow g.arrow _)

/-- `Φ.toFunctor` sends `⟨i, x⟩` to `⟨Φ.index i, Φ.obj i x⟩`. -/
@[simp]
theorem toFunctor_obj (Φ : 𝓐.Hom 𝓑) (x : 𝓐.Obj) :
    Φ.toFunctor.obj x = ⟨Φ.index x.chart, Φ.obj x.chart x.point⟩ := (rfl)

/-- Chart index of `Φ.toFunctor.obj x`. -/
theorem chart_toFunctor_obj (Φ : 𝓐.Hom 𝓑) (x : 𝓐.Obj) :
    (Φ.toFunctor.obj x).chart = Φ.index x.chart := (rfl)

/-- Point of `Φ.toFunctor.obj x`. -/
@[simp]
theorem point_toFunctor_obj (Φ : 𝓐.Hom 𝓑) (x : 𝓐.Obj) :
    (Φ.toFunctor.obj x).point = Φ.obj x.chart x.point := (rfl)

/-- `Φ.toFunctor` applies `Φ.map` to the underlying overlap arrow. -/
@[simp]
theorem toFunctor_map_arrow (Φ : 𝓐.Hom 𝓑) {x y : 𝓐.Obj} (f : x ⟶ y) :
    (Φ.toFunctor.map f).arrow = Φ.map f.arrow := (rfl)

/-- The identity atlas morphism induces the identity functor on `𝓐.Obj`. -/
@[simp]
theorem toFunctor_id (𝓐 : ChartAtlas G U R) : (Hom.id 𝓐).toFunctor = 𝟭 𝓐.Obj := (rfl)

/-- Composition of atlas morphisms induces composition of presenting-groupoid functors. -/
@[simp]
theorem toFunctor_comp {μ : Type*} {G'' : μ → Type*} [∀ m, Group (G'' m)]
    {U'' : μ → Type*} [∀ m, MulAction (G'' m) (U'' m)]
    {R'' : μ → μ → Type*} [∀ m n, MulAction (G'' n) (R'' m n)]
    {𝓒 : ChartAtlas G'' U'' R''} (Ψ : 𝓑.Hom 𝓒) (Φ : 𝓐.Hom 𝓑) :
    (Ψ.comp Φ).toFunctor = Φ.toFunctor ⋙ Ψ.toFunctor := (rfl)

/-- An atlas morphism intertwines the chart inclusion functors via `ActionCategory.map`. -/
theorem chartFunctor_comp_toFunctor (Φ : 𝓐.Hom 𝓑) (i : ι) :
    𝓐.chartFunctor i ⋙ Φ.toFunctor =
      ActionCategory.map (Φ.groupHom i) ⟨Φ.obj i, Φ.obj_smul i⟩ ⋙ 𝓑.chartFunctor (Φ.index i) := by
  have hhext : ∀ {x₁ x₂ y₁ y₂ : 𝓑.Obj}, x₁ = x₂ → y₁ = y₂ →
      ∀ (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂), HEq f₁.arrow f₂.arrow → HEq f₁ f₂ := by
    rintro _ _ _ _ rfl rfl _ _ h
    exact heq_of_eq (Obj.Hom.ext (eq_of_heq h))
  have hobj (a : ActionCategory (G i) (U i)) :
      (𝓐.chartFunctor i ⋙ Φ.toFunctor).obj a =
        (ActionCategory.map (Φ.groupHom i) ⟨Φ.obj i, Φ.obj_smul i⟩ ⋙
          𝓑.chartFunctor (Φ.index i)).obj a :=
    congrArg (Obj.mk (Φ.index i))
      (ActionCategory.back_map_obj (Φ.groupHom i) ⟨Φ.obj i, Φ.obj_smul i⟩ a).symm
  refine CategoryTheory.Functor.hext hobj fun a b f ↦ hhext (hobj a) (hobj b) _ _ (heq_of_eq ?_)
  dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.comp_map, chartFunctor,
    toFunctor]
  rw [Φ.map_smul, Φ.map_unit, ActionCategory.map_map_hom, ActionCategory.back_map_obj]
  rfl

/-- `Φ.toFunctor` is faithful precisely when `Φ.map` is injective on arrows sharing the same
endpoints in `U i` and `U j`. -/
theorem faithful_toFunctor_iff (Φ : 𝓐.Hom 𝓑) :
    Φ.toFunctor.Faithful ↔
      ∀ {i j : ι} (α β : R i j), 𝓐.src α = 𝓐.src β → 𝓐.tgt α = 𝓐.tgt β →
        Φ.map α = Φ.map β → α = β := by
  constructor
  · intro h i j α β hs ht hmap
    have : Φ.toFunctor.Faithful := h
    let f₁ : (⟨i, 𝓐.src α⟩ : 𝓐.Obj) ⟶ ⟨j, 𝓐.tgt α⟩ := ⟨α, rfl, rfl⟩
    let f₂ : (⟨i, 𝓐.src α⟩ : 𝓐.Obj) ⟶ ⟨j, 𝓐.tgt α⟩ := ⟨β, hs.symm, ht.symm⟩
    exact congrArg Obj.Hom.arrow
      (Φ.toFunctor.map_injective (a₁ := f₁) (a₂ := f₂) (Obj.Hom.ext hmap))
  · exact fun h ↦ ⟨fun {_ _} f₁ f₂ hm ↦ Obj.Hom.ext <|
      h f₁.arrow f₂.arrow (f₁.src_arrow.trans f₂.src_arrow.symm)
        (f₁.tgt_arrow.trans f₂.tgt_arrow.symm) (congrArg Obj.Hom.arrow hm)⟩

/-- `Φ.toFunctor` is full precisely when every overlap arrow in `𝓑` between images of chart points
lifts to an overlap arrow in `𝓐` with those endpoints. -/
theorem full_toFunctor_iff (Φ : 𝓐.Hom 𝓑) :
    Φ.toFunctor.Full ↔
      ∀ {i j : ι} (x : U i) (y : U j) (β : R' (Φ.index i) (Φ.index j)),
        𝓑.src β = Φ.obj i x → 𝓑.tgt β = Φ.obj j y →
          ∃ α : R i j, 𝓐.src α = x ∧ 𝓐.tgt α = y ∧ Φ.map α = β := by
  constructor
  · intro h i j x y β hs ht
    have : Φ.toFunctor.Full := h
    let g : Φ.toFunctor.obj ⟨i, x⟩ ⟶ Φ.toFunctor.obj ⟨j, y⟩ := ⟨β, hs, ht⟩
    obtain ⟨f, hf⟩ := Φ.toFunctor.map_surjective g
    exact ⟨f.arrow, f.src_arrow, f.tgt_arrow, congrArg Obj.Hom.arrow hf⟩
  · refine fun h ↦ ⟨fun {x y} g ↦ ?_⟩
    obtain ⟨α, hs, ht, hm⟩ := h x.point y.point g.arrow g.src_arrow g.tgt_arrow
    exact ⟨⟨α, hs, ht⟩, Obj.Hom.ext hm⟩

end Hom

/-- A natural transformation between two chart-atlas morphisms `Φ Ψ : 𝓐.Hom 𝓑`: a family of
overlap arrows `app i x : R' (Φ.index i) (Ψ.index i)` in `𝓑` from `Φ.obj i x` to `Ψ.obj i x`
commuting with all overlap arrows of `𝓐`. -/
@[ext]
structure NatTrans {𝓐 : ChartAtlas G U R} {𝓑 : ChartAtlas G' U' R'} (Φ Ψ : 𝓐.Hom 𝓑) where
  /-- Component overlap arrow at `x : U i`. -/
  app : ∀ (i : ι), U i → R' (Φ.index i) (Ψ.index i)
  /-- Source of `app i x` is `Φ.obj i x`. -/
  src_app : ∀ (i : ι) (x : U i), 𝓑.src (app i x) = Φ.obj i x
  /-- Target of `app i x` is `Ψ.obj i x`. -/
  tgt_app : ∀ (i : ι) (x : U i), 𝓑.tgt (app i x) = Ψ.obj i x
  /-- Naturality square in `𝓑` for every overlap arrow `α : R i j` in `𝓐`. -/
  naturality : ∀ {i j : ι} (α : R i j),
    𝓑.comp (Φ.map α) (app j (𝓐.tgt α)) ((Φ.tgt_map α).trans (src_app j _).symm) =
      𝓑.comp (app i (𝓐.src α)) (Ψ.map α) ((tgt_app i _).trans (Ψ.src_map α).symm)

namespace NatTrans

variable {𝓐 : ChartAtlas G U R} {𝓑 : ChartAtlas G' U' R'}

attribute [simp] src_app tgt_app

/-- The categorical natural transformation `Φ.toFunctor ⟶ Ψ.toFunctor` induced by `η`. -/
def toNatTrans {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) : Φ.toFunctor ⟶ Ψ.toFunctor where
  app x := ⟨η.app x.chart x.point, η.src_app _ _, η.tgt_app _ _⟩
  naturality {x y} f := Obj.Hom.ext <|
    (𝓑.comp_congr rfl (congrArg (η.app y.chart) f.tgt_arrow.symm) _ _).trans
      ((η.naturality f.arrow).trans
        (𝓑.comp_congr (congrArg (η.app x.chart) f.src_arrow) rfl _ _))

/-- Component arrow of `η.toNatTrans` at `x`. -/
@[simp]
theorem toNatTrans_app_arrow {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) (x : 𝓐.Obj) :
    (η.toNatTrans.app x).arrow = η.app x.chart x.point := (rfl)

/-- The identity natural transformation on an atlas morphism `Φ`. -/
def refl (Φ : 𝓐.Hom 𝓑) : NatTrans Φ Φ where
  app i x := 𝓑.unit (Φ.index i) (Φ.obj i x)
  src_app i x := 𝓑.src_unit _ _
  tgt_app i x := 𝓑.tgt_unit _ _
  naturality _ := by simp

/-- The inverse natural transformation of `η : NatTrans Φ Ψ`, formed using `𝓑.inv`. -/
def symm {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) : NatTrans Ψ Φ where
  app i x := 𝓑.inv (η.app i x)
  src_app i x := (𝓑.src_inv _).trans (η.tgt_app i x)
  tgt_app i x := (𝓑.tgt_inv _).trans (η.src_app i x)
  naturality {i j} α := by
    have h₁ := 𝓑.comp_congr (η.naturality α).symm (rfl : 𝓑.inv (η.app j (𝓐.tgt α)) = _)
      (by simp) (by simp)
    calc 𝓑.comp (Ψ.map α) (𝓑.inv (η.app j (𝓐.tgt α))) _
        = 𝓑.comp (𝓑.comp (𝓑.inv (η.app i (𝓐.src α))) (η.app i (𝓐.src α)) (by simp))
            (𝓑.comp (Ψ.map α) (𝓑.inv (η.app j (𝓐.tgt α))) (by simp)) (by simp) := by simp
      _ = 𝓑.comp (𝓑.inv (η.app i (𝓐.src α)))
            (𝓑.comp (η.app i (𝓐.src α))
              (𝓑.comp (Ψ.map α) (𝓑.inv (η.app j (𝓐.tgt α))) (by simp)) (by simp))
            (by simp) := 𝓑.comp_assoc _ _ _ _ _
      _ = 𝓑.comp (𝓑.inv (η.app i (𝓐.src α)))
            (𝓑.comp (𝓑.comp (η.app i (𝓐.src α)) (Ψ.map α) (by simp))
              (𝓑.inv (η.app j (𝓐.tgt α))) (by simp)) (by simp) :=
          𝓑.comp_congr rfl (𝓑.comp_assoc _ _ _ (by simp) (by simp)).symm _ _
      _ = 𝓑.comp (𝓑.inv (η.app i (𝓐.src α)))
            (𝓑.comp (𝓑.comp (Φ.map α) (η.app j (𝓐.tgt α)) (by simp))
              (𝓑.inv (η.app j (𝓐.tgt α))) (by simp)) (by simp) :=
          𝓑.comp_congr rfl h₁ _ _
      _ = 𝓑.comp (𝓑.inv (η.app i (𝓐.src α))) (Φ.map α) _ :=
          𝓑.comp_congr rfl ((𝓑.comp_assoc _ _ _ (by simp) (by simp)).trans (by simp)) _ _

/-- Vertical composition of natural transformations between atlas morphisms. -/
def trans {Φ Ψ Θ : 𝓐.Hom 𝓑} (η₁ : NatTrans Φ Ψ) (η₂ : NatTrans Ψ Θ) : NatTrans Φ Θ where
  app i x := 𝓑.comp (η₁.app i x) (η₂.app i x) ((η₁.tgt_app i x).trans (η₂.src_app i x).symm)
  src_app i x := (𝓑.src_comp _ _ _).trans (η₁.src_app i x)
  tgt_app i x := (𝓑.tgt_comp _ _ _).trans (η₂.tgt_app i x)
  naturality α :=
    (𝓑.comp_assoc _ _ _ _ _).symm.trans <|
      (𝓑.comp_congr (η₁.naturality α) rfl _ _).trans <|
        (𝓑.comp_assoc _ _ _ _ _).trans <|
          (𝓑.comp_congr rfl (η₂.naturality α) _ _).trans
            (𝓑.comp_assoc _ _ _ _ _).symm

/-- Because `𝓑.Obj` is a groupoid, a natural transformation of atlas morphisms induces a natural
isomorphism `Φ.toFunctor ≅ Ψ.toFunctor` between the induced functors on presenting groupoids. -/
def toNatIso {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) : Φ.toFunctor ≅ Ψ.toFunctor where
  hom := η.toNatTrans
  inv := η.symm.toNatTrans
  hom_inv_id := by
    ext x
    apply Obj.Hom.ext
    simp only [CategoryTheory.NatTrans.comp_app, comp_arrow, toNatTrans_app_arrow, symm,
      CategoryTheory.NatTrans.id_app, id_arrow, Hom.point_toFunctor_obj]
    exact (𝓑.comp_inv _).trans (congrArg _ (η.src_app _ _))
  inv_hom_id := by
    ext x
    apply Obj.Hom.ext
    simp only [CategoryTheory.NatTrans.comp_app, comp_arrow, toNatTrans_app_arrow, symm,
      CategoryTheory.NatTrans.id_app, id_arrow, Hom.point_toFunctor_obj]
    exact (𝓑.inv_comp _).trans (congrArg _ (η.tgt_app _ _))

/-- The component overlap arrow of `η.toNatIso.hom` at `x` is `η.app x.chart x.point`. -/
@[simp]
theorem toNatIso_hom_app_arrow {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) (x : 𝓐.Obj) :
    (η.toNatIso.hom.app x).arrow = η.app x.chart x.point := (rfl)

/-- `NatTrans.refl` induces `Iso.refl` on `Φ.toFunctor`. -/
@[simp]
theorem toNatIso_refl (Φ : 𝓐.Hom 𝓑) : (refl Φ).toNatIso = Iso.refl Φ.toFunctor := by
  ext x
  apply Obj.Hom.ext
  simp only [toNatIso, toNatTrans_app_arrow, refl, Iso.refl_hom, CategoryTheory.NatTrans.id_app,
    id_arrow, Hom.point_toFunctor_obj]
  rfl

/-- `NatTrans.symm` induces `Iso.symm` on presenting-groupoid functors. -/
@[simp]
theorem toNatIso_symm {Φ Ψ : 𝓐.Hom 𝓑} (η : NatTrans Φ Ψ) :
    η.symm.toNatIso = η.toNatIso.symm := by
  ext x
  apply Obj.Hom.ext
  simp only [toNatIso, toNatTrans_app_arrow, symm, Iso.symm_hom]
  rfl

/-- `NatTrans.trans` induces `Iso.trans` on presenting-groupoid functors. -/
@[simp]
theorem toNatIso_trans {Φ Ψ Θ : 𝓐.Hom 𝓑} (η₁ : NatTrans Φ Ψ) (η₂ : NatTrans Ψ Θ) :
    (η₁.trans η₂).toNatIso = η₁.toNatIso ≪≫ η₂.toNatIso := by
  ext x
  apply Obj.Hom.ext
  simp only [toNatIso, toNatTrans_app_arrow, trans, Iso.trans_hom,
    CategoryTheory.NatTrans.comp_app, comp_arrow]
  rfl

end NatTrans

end HomAndNatTrans

end ChartAtlas

end TauCeti
