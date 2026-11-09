/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homeomorph.Quotient
public import TauCeti.Topology.FiberBundle.GroupCocycle
public import TauCeti.Topology.FiberBundle.Trivialization
public import TauCeti.Topology.Maps.LocalSections

/-!
# Associated bundles

Let `P` be a principal `G`-bundle over `B` and let `G` act continuously on the left on a space
`F`. The *associated bundle* `P ×_G F` is the quotient of `P × F` (pairs over a common base point)
by `(p • g, v) ∼ (p, g • v)`. Its points over `b` are the classes `[p, v]` of a point `p` of the
fibre of `P` over `b` and of `v : F`. It is a fibre bundle over `B` with model fibre `F`.

Here `TauCeti.AssociatedBundle G P F` is constructed by gluing local products: its charts are
indexed by the base points `b`, the chart at `b` has the base set of the preferred trivialization
`e_b = trivializationAt G P b` of `P`, and the transition from the chart at `b` to the chart at
`b'` acts on `F` by the transition function `x ↦ e_b.coordChange e_b' x 1` of `P`. These
transition functions are continuous (`Bundle.Trivialization.continuousOn_coordChange`) and form a
`G`-valued cocycle, because the coordinate changes of a principal bundle are left multiplications
(`Bundle.Trivialization.coordChange_one_mul_coordChange_one`); so the glued bundle is
`TauCeti.fiberBundleCoreOfGroupCocycle`. Its total space is Hausdorff when `B`
and `F` are (`TauCeti.FiberBundle.t2Space_totalSpace`).

The class `[p, v]` is `TauCeti.AssociatedBundle.mk G p v`, the point with coordinate `(e p).2 • v`
in the chart at its base point `b`, where `e = trivializationAt G P b`. In every chart the same
formula holds with the corresponding trivialization of `P`
(`TauCeti.AssociatedBundle.trivializationAt_mk`): the charts of the associated bundle intertwine
the action of `G` on `F` with the charts of `P`. The class map identifies `P ×_G F` with the
quotient: `[p • g, v] = [p, g • v]` (`TauCeti.AssociatedBundle.mk_smul`), two classes agree
exactly when the pairs differ by the action (`TauCeti.AssociatedBundle.mk_eq_mk_iff`), and the map
`(p, v) ↦ [p, v]` on the total spaces is an open quotient map
(`TauCeti.AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk`). Hence the total space of the
associated bundle is homeomorphic to the quotient of `P × F` by the orbit relation
(`TauCeti.AssociatedBundle.quotientHomeomorph`).

## Main definitions

* `TauCeti.associatedBundleCore G P F`: the fibre bundle core glued from the transition functions
  of `P` acting on `F`.
* `TauCeti.AssociatedBundle G P F`: the associated bundle `P ×_G F`.
* `TauCeti.AssociatedBundle.mk G p v`: the class `[p, v]`.
* `TauCeti.AssociatedBundle.orbitRel G P F`: the relation `(p • g, v) ∼ (p, g • v)` on pairs of
  points of the total space of `P` and of `F`.
* `TauCeti.AssociatedBundle.quotientHomeomorph G P F`: the homeomorphism from the quotient by this
  relation onto the total space of the associated bundle.

## Main results

* `TauCeti.AssociatedBundle.trivializationAt_mk`: the charts of the associated bundle in terms of
  the charts of `P`.
* `TauCeti.AssociatedBundle.mk_smul` and `TauCeti.AssociatedBundle.mk_eq_mk_iff`: the classes are
  the orbits of `(p, v) ↦ (p • g, g⁻¹ • v)`.
* `TauCeti.AssociatedBundle.mk_bijective`: each point `p` of a fibre of `P` identifies `F` with
  the fibre of the associated bundle.
* `Continuous.totalSpaceMk_associatedBundleMk`: the class of a continuous family of pairs is
  continuous.
* `TauCeti.AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk`: `(p, v) ↦ [p, v]` is an open
  quotient map.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.7 (associated bundles, glued from the transition functions of the principal bundle and
  identified with the quotient of `P × F`).
* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4, §5 (the fibre bundle `P ×_G F` associated with a principal bundle).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §8 (the bundle
  associated with a coordinate bundle and a new fibre).
-/

public section

open Bundle Filter MulOpposite Set Topology

namespace TauCeti

/-! ### The associated bundle -/

variable (G : Type*) {B : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  (P : B → Type*) [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  (F : Type*) [TopologicalSpace F] [MulAction G F] [ContinuousSMul G F]

/-- The fibre bundle core of the bundle associated with the principal bundle `P` and the action of
`G` on `F`. Its charts are indexed by the points `b` of the base, the chart at `b` has the base set
of `trivializationAt G P b`, and the transition from the chart at `b` to the chart at `b'` acts on
`F` by the transition function `x ↦ (trivializationAt G P b).coordChange (trivializationAt G P b')
x 1` of `P`. -/
noncomputable def associatedBundleCore : FiberBundleCore B B F :=
  fiberBundleCoreOfGroupCocycle (fun b ↦ (trivializationAt G P b).baseSet)
    (fun b b' x ↦ (trivializationAt G P b).coordChange (trivializationAt G P b') x 1)
    (fun _ _ _ _ hx ↦ Trivialization.coordChange_one_mul_coordChange_one _ _ _ hx.1.1 hx.1.2 hx.2)
    F (fun b ↦ (trivializationAt G P b).open_baseSet) id (mem_baseSet_trivializationAt G P)
    fun b b' ↦ ((trivializationAt G P b).continuousOn_coordChange (trivializationAt G P b')).comp
      (continuousOn_id.prodMk continuousOn_const) fun _ hx ↦ ⟨hx, mem_univ _⟩

/-- The associated bundle core is glued from the transition functions of `P` acting on `F`. -/
theorem associatedBundleCore_def :
    associatedBundleCore G P F =
      fiberBundleCoreOfGroupCocycle (fun b ↦ (trivializationAt G P b).baseSet)
        (fun b b' x ↦ (trivializationAt G P b).coordChange (trivializationAt G P b') x 1)
        (fun _ _ _ _ hx ↦
          Trivialization.coordChange_one_mul_coordChange_one _ _ _ hx.1.1 hx.1.2 hx.2)
        F (fun b ↦ (trivializationAt G P b).open_baseSet) id (mem_baseSet_trivializationAt G P)
        fun b b' ↦ ((trivializationAt G P b).continuousOn_coordChange
          (trivializationAt G P b')).comp (continuousOn_id.prodMk continuousOn_const)
            fun _ hx ↦ ⟨hx, mem_univ _⟩ :=
  (rfl)

variable {G P F} in
/-- The preferred chart of the associated bundle core at `b` is the chart of index `b`. -/
@[simp]
theorem associatedBundleCore_indexAt (b : B) : (associatedBundleCore G P F).indexAt b = b := by
  rw [associatedBundleCore_def, fiberBundleCoreOfGroupCocycle_indexAt, id]

variable {G P F} in
/-- The chart of index `b` of the associated bundle core has the base set of
`trivializationAt G P b`. -/
@[simp]
theorem associatedBundleCore_localTriv_baseSet (b : B) :
    ((associatedBundleCore G P F).localTriv b).baseSet = (trivializationAt G P b).baseSet := by
  rw [associatedBundleCore_def, fiberBundleCoreOfGroupCocycle_localTriv_baseSet]

variable {G P F} in
/-- The coordinate change of the associated bundle core from the chart of index `b` to the chart of
index `b'` is the action of the transition function of `P`. -/
@[simp]
theorem associatedBundleCore_coordChange (b b' x : B) (v : F) :
    (associatedBundleCore G P F).coordChange b b' x v =
      (trivializationAt G P b).coordChange (trivializationAt G P b') x 1 • v := by
  rw [associatedBundleCore_def, fiberBundleCoreOfGroupCocycle_coordChange]

/-- The *associated bundle* `P ×_G F` of a principal `G`-bundle `P` and a left action of `G` on
`F`: the fibre bundle with model fibre `F` glued from the transition functions of `P` acting on
`F`. Its point over `b` with coordinate `v` in the chart at `b` is the class `[p, v]` of the point
`p` of `P` with coordinate `1` in `trivializationAt G P b` (`TauCeti.AssociatedBundle.mk`). -/
abbrev AssociatedBundle : B → Type _ :=
  (associatedBundleCore G P F).Fiber

namespace AssociatedBundle

variable {G P F}

/-- The preferred trivializations of the associated bundle are the charts of its core. -/
theorem trivializationAt_eq_localTriv (b : B) :
    trivializationAt F (AssociatedBundle G P F) b = (associatedBundleCore G P F).localTriv b :=
  -- The preferred trivialization at `b` is, by definition, the chart of index `indexAt b`.
  congrArg (associatedBundleCore G P F).localTriv (associatedBundleCore_indexAt b)

/-- The preferred trivialization of the associated bundle at `b` has the base set of the preferred
trivialization of `P` at `b`. -/
@[simp]
theorem baseSet_trivializationAt (b : B) :
    (trivializationAt F (AssociatedBundle G P F) b).baseSet = (trivializationAt G P b).baseSet := by
  rw [trivializationAt_eq_localTriv, associatedBundleCore_localTriv_baseSet]

variable (G) in
/-- The class `[p, v]` in the associated bundle of a point `p` of the fibre of `P` over `b` and of
`v : F`: the point over `b` with coordinate `(e p).2 • v` in the chart at `b`, where
`e = trivializationAt G P b`. It satisfies `[p • g, v] = [p, g • v]`
(`TauCeti.AssociatedBundle.mk_smul`), and in every chart its coordinate is given by the same
formula (`TauCeti.AssociatedBundle.trivializationAt_mk`). The group `G` is explicit, since the
fibres of `P` alone do not determine it. -/
noncomputable def mk {b : B} (p : P b) (v : F) : AssociatedBundle G P F b :=
  -- The fibre is a type synonym of `F`, so the action of `G` on `F` is supplied explicitly.
  @HSMul.hSMul G F F _ (trivializationAt G P b ⟨b, p⟩).2 v

/-- **The charts of the associated bundle.** In the preferred trivialization at `b'`, the class
`[p, v]` over a point `b` of its base set has coordinate `(e p).2 • v`, where
`e = trivializationAt G P b'`. -/
theorem trivializationAt_mk {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet) (p : P b)
    (v : F) :
    trivializationAt F (AssociatedBundle G P F) b' ⟨b, mk G p v⟩ =
      (b, (trivializationAt G P b' ⟨b, p⟩).2 • v) := by
  rw [trivializationAt_eq_localTriv, FiberBundleCore.localTriv_apply,
    associatedBundleCore_indexAt]
  refine Prod.ext rfl ((associatedBundleCore_coordChange (F := F) b b' b (mk G p v)).trans ?_)
  have hb₀ := mem_baseSet_trivializationAt G P b
  rw [mk, smul_smul, ← (trivializationAt G P b).coordChange_eq_mul _ hb₀ hb]
  exact congrArg (· • v) ((trivializationAt G P b).coordChange_apply_snd _ (p := ⟨b, p⟩) hb₀)

/-- The second coordinate of the class `[p, v]` in the preferred trivialization at `b'`. -/
theorem trivializationAt_mk_snd {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet) (p : P b)
    (v : F) :
    (trivializationAt F (AssociatedBundle G P F) b' ⟨b, mk G p v⟩).2 =
      (trivializationAt G P b' ⟨b, p⟩).2 • v := by
  rw [trivializationAt_mk hb]

/-- **The classes are the orbits of the action.** The classes of `(p • g, v)` and of
`(p, g • v)` agree. -/
@[simp]
theorem mk_smul {b : B} (p : P b) (g : G) (v : F) : mk G (op g • p) v = mk G p (g • v) := by
  have hb := mem_baseSet_trivializationAt G P b
  rw [mk, mk, (trivializationAt G P b).snd_apply_smul hb, mul_smul]

/-- Two classes over the same point agree exactly when the second components differ by the
division map of the first ones: `[p, v] = [q, w]` if and only if `v = (division G p q) • w`. -/
theorem mk_eq_mk_iff {b : B} {p q : P b} {v w : F} :
    mk G p v = mk G q w ↔ v = PrincipalBundle.division G p q • w := by
  have hb := mem_baseSet_trivializationAt G P b
  rw [mk, mk, PrincipalBundle.division_eq_of_mem_baseSet hb, mul_smul, eq_inv_smul_iff]
  -- The left side is an equation in the fibre, a type synonym of `F`.
  exact Iff.rfl

/-- The classes `[p, v]` with a fixed first component `p` exhaust the fibre exactly once: `p`
identifies `F` with the fibre of the associated bundle over its base point. -/
theorem mk_bijective {b : B} (p : P b) :
    Function.Bijective (mk G p : F → AssociatedBundle G P F b) := by
  -- By definition, the map is the action of `(e p).2` on `F`, a bijection.
  unfold mk
  exact MulAction.bijective _

/-! ### The quotient topology -/

/-- The class of `(p • g, g⁻¹ • v)` is the class of `(p, v)`. -/
theorem mk_smul_inv_smul {b : B} (p : P b) (g : G) (v : F) :
    mk G (op g • p) (g⁻¹ • v) = mk G p v := by
  rw [mk_smul, smul_inv_smul]

/-- Two pairs of points of the total space of `P` and of `F` have the same class exactly when they
differ by the action of an element `g` of `G`, acting by `(p, v) ↦ (p • g, g⁻¹ • v)`. -/
theorem totalSpaceMk_mk_eq_iff {x y : TotalSpace G P × F} :
    (⟨x.1.proj, mk G x.1.2 x.2⟩ : TotalSpace F (AssociatedBundle G P F)) =
        ⟨y.1.proj, mk G y.1.2 y.2⟩ ↔
      ∃ g : G, y = (⟨x.1.proj, op g • x.1.2⟩, g⁻¹ • x.2) := by
  obtain ⟨⟨b, p⟩, v⟩ := x
  obtain ⟨⟨b', q⟩, w⟩ := y
  constructor
  · intro h
    obtain rfl : b = b' := congrArg TotalSpace.proj h
    refine ⟨PrincipalBundle.division G p q, ?_⟩
    rw [TotalSpace.mk_inj, mk_eq_mk_iff] at h
    rw [h, inv_smul_smul, PrincipalBundle.smul_division]
  · rintro ⟨g, h⟩
    simp only [Prod.mk.injEq, TotalSpace.mk.injEq] at h
    obtain ⟨⟨rfl, hq⟩, rfl⟩ := h
    rw [eq_of_heq hq, mk_smul_inv_smul]

variable (G P F) in
/-- The relation on pairs of points of the total space of `P` and of `F` identifying `(p, v)` with
`(p • g, g⁻¹ • v)` for every `g : G`. Its quotient is the associated bundle
(`TauCeti.AssociatedBundle.quotientHomeomorph`). -/
def orbitRel : Setoid (TotalSpace G P × F) where
  r x y := ∃ g : G, y = (⟨x.1.proj, op g • x.1.2⟩, g⁻¹ • x.2)
  -- By `totalSpaceMk_mk_eq_iff`, the relation says that the two pairs have the same class.
  iseqv.refl _ := totalSpaceMk_mk_eq_iff.1 rfl
  iseqv.symm h := totalSpaceMk_mk_eq_iff.1 (totalSpaceMk_mk_eq_iff.2 h).symm
  iseqv.trans h h' := totalSpaceMk_mk_eq_iff.1
    ((totalSpaceMk_mk_eq_iff.2 h).trans (totalSpaceMk_mk_eq_iff.2 h'))

/-- Two pairs are related by `orbitRel` when they differ by the action of an element of `G`. -/
theorem orbitRel_iff {x y : TotalSpace G P × F} :
    orbitRel G P F x y ↔ ∃ g : G, y = (⟨x.1.proj, op g • x.1.2⟩, g⁻¹ • x.2) :=
  Iff.rfl

/-- The orbit relation is the kernel of `(p, v) ↦ [p, v]`. -/
theorem orbitRel_eq_ker :
    orbitRel G P F = Setoid.ker fun x : TotalSpace G P × F ↦
      (⟨x.1.proj, mk G x.1.2 x.2⟩ : TotalSpace F (AssociatedBundle G P F)) :=
  Setoid.ext fun _ _ ↦ totalSpaceMk_mk_eq_iff.symm

end AssociatedBundle

end TauCeti

/-! ### Continuity of classes -/

open TauCeti TauCeti.AssociatedBundle

variable {G B : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {F : Type*} [TopologicalSpace F] [MulAction G F] [ContinuousSMul G F]
  {X : Type*} [TopologicalSpace X] {f : X → B} {p : ∀ x, P (f x)} {v : X → F} {s : Set X}
  {x₀ : X}

/-- **Classes depend continuously on the pair.** For a continuous family of points `⟨f x, p x⟩`
of the total space of `P` and a continuous family `v x` of points of `F`, the classes
`[p x, v x]` form a continuous family in the total space of the associated bundle. -/
theorem ContinuousWithinAt.totalSpaceMk_associatedBundleMk
    (hp : ContinuousWithinAt (fun x ↦ TotalSpace.mk' G (f x) (p x)) s x₀)
    (hv : ContinuousWithinAt v s x₀) :
    ContinuousWithinAt
      (fun x ↦ TotalSpace.mk' F (f x) (AssociatedBundle.mk G (p x) (v x))) s x₀ := by
  set e := trivializationAt G P (f x₀)
  have hx₀ := mem_baseSet_trivializationAt G P (f x₀)
  have hf : ContinuousWithinAt f s x₀ :=
    (FiberBundle.continuous_proj G P).continuousAt.comp_continuousWithinAt hp
  refine (FiberBundle.continuousWithinAt_totalSpace F _).2 ⟨hf, ?_⟩
  -- Near `x₀`, the coordinate of the class in the chart at `f x₀` is `(e (p x)).2 • v x`.
  have he : ContinuousWithinAt (fun x ↦ (e ⟨f x, p x⟩).2 • v x) s x₀ :=
    (continuous_snd.continuousAt.comp_continuousWithinAt
      ((e.continuousAt (e.mem_source.2 hx₀)).comp_continuousWithinAt hp)).smul hv
  refine he.congr_of_eventuallyEq ?_ (trivializationAt_mk_snd hx₀ _ _)
  filter_upwards [hf (e.open_baseSet.mem_nhds hx₀)] with x hx
  exact trivializationAt_mk_snd hx _ _

/-- Classes of a family of pairs continuous at a point are continuous at that point. -/
theorem ContinuousAt.totalSpaceMk_associatedBundleMk
    (hp : ContinuousAt (fun x ↦ TotalSpace.mk' G (f x) (p x)) x₀) (hv : ContinuousAt v x₀) :
    ContinuousAt
      (fun x ↦ TotalSpace.mk' F (f x) (AssociatedBundle.mk G (p x) (v x))) x₀ :=
  (continuousWithinAt_univ _ _).1 <|
    hp.continuousWithinAt.totalSpaceMk_associatedBundleMk (s := univ) hv.continuousWithinAt

/-- Classes of a family of pairs continuous on a set are continuous on that set. -/
theorem ContinuousOn.totalSpaceMk_associatedBundleMk
    (hp : ContinuousOn (fun x ↦ TotalSpace.mk' G (f x) (p x)) s) (hv : ContinuousOn v s) :
    ContinuousOn
      (fun x ↦ TotalSpace.mk' F (f x) (AssociatedBundle.mk G (p x) (v x))) s :=
  fun x hx ↦ (hp x hx).totalSpaceMk_associatedBundleMk (hv x hx)

/-- Classes of a continuous family of pairs form a continuous family. -/
theorem Continuous.totalSpaceMk_associatedBundleMk
    (hp : Continuous fun x ↦ TotalSpace.mk' G (f x) (p x)) (hv : Continuous v) :
    Continuous fun x ↦ TotalSpace.mk' F (f x) (AssociatedBundle.mk G (p x) (v x)) :=
  continuous_iff_continuousAt.2 fun _ ↦ hp.continuousAt.totalSpaceMk_associatedBundleMk
    hv.continuousAt

namespace TauCeti.AssociatedBundle

variable (G P F)

/-- The map `(p, v) ↦ [p, v]` from pairs of points of the total space of `P` and of `F` to the
total space of the associated bundle is continuous. -/
theorem continuous_totalSpaceMk_mk :
    Continuous fun x : TotalSpace G P × F ↦
      (⟨x.1.proj, mk G x.1.2 x.2⟩ : TotalSpace F (AssociatedBundle G P F)) :=
  Continuous.totalSpaceMk_associatedBundleMk (f := fun x : TotalSpace G P × F ↦ x.1.proj)
    continuous_fst continuous_snd

/-- The map `(p, v) ↦ [p, v]` is an open map. -/
theorem isOpenMap_totalSpaceMk_mk :
    IsOpenMap fun x : TotalSpace G P × F ↦
      (⟨x.1.proj, mk G x.1.2 x.2⟩ : TotalSpace F (AssociatedBundle G P F)) := by
  refine IsOpenMap.of_local_sections fun x₀ ↦ ?_
  set Φ := fun x : TotalSpace G P × F ↦
    (⟨x.1.proj, mk G x.1.2 x.2⟩ : TotalSpace F (AssociatedBundle G P F))
  set e := trivializationAt G P x₀.1.proj
  set eA := trivializationAt F (AssociatedBundle G P F) x₀.1.proj
  have heA : eA.baseSet = e.baseSet := baseSet_trivializationAt _
  have hb₀ : x₀.1.proj ∈ e.baseSet := mem_baseSet_trivializationAt G P x₀.1.proj
  set g₀ := (e x₀.1).2
  -- The local continuous section `ψ` through `x₀ = (p₀, v₀)` over `b₀`: it sends a point `y` of
  -- the associated bundle near `[p₀, v₀]` to the pair of the point of `P` over the base point of
  -- `y` whose coordinate in the chart `e` is `g₀ = (e p₀).2`, and of `g₀⁻¹` applied to the
  -- coordinate of `y` in the chart at `b₀`.
  set ψ : TotalSpace F (AssociatedBundle G P F) → TotalSpace G P × F :=
    fun y ↦ (e.toOpenPartialHomeomorph.symm (y.proj, g₀), g₀⁻¹ • (eA y).2)
  have hψ₀ : ψ (Φ x₀) = x₀ := by
    refine Prod.ext (e.symm_apply_mk_proj (e.mem_source.2 hb₀)) ?_
    simp only [ψ, Φ, eA]
    rw [trivializationAt_mk_snd hb₀, TotalSpace.eta, inv_smul_smul]
  have hψ : ContinuousAt ψ (Φ x₀) := by
    refine ContinuousAt.prodMk ?_ ?_
    · exact (e.toOpenPartialHomeomorph.continuousAt_symm (e.mem_target.2 hb₀)).comp
        ((FiberBundle.continuous_proj F _).continuousAt.prodMk continuousAt_const)
    · exact (continuous_snd.continuousAt.comp
        (eA.continuousAt (eA.mem_source.2 (heA ▸ hb₀)))).const_smul _
  -- Over the base set of `e`, the section `ψ` is a right inverse of `Φ`.
  have hΦψ : ∀ y : TotalSpace F (AssociatedBundle G P F), y.proj ∈ e.baseSet → Φ (ψ y) = y := by
    intro y hy
    have hσ : (e.toOpenPartialHomeomorph.symm (y.proj, g₀)).proj = y.proj :=
      e.proj_symm_apply' hy
    have hyA : y.proj ∈ eA.baseSet := heA ▸ hy
    have hσA : (Φ (ψ y)).proj ∈ eA.baseSet := hσ ▸ hyA
    refine eA.toOpenPartialHomeomorph.injOn (eA.mem_source.2 hσA) (eA.mem_source.2 hyA) ?_
    rw [eA.coe_coe]
    refine Prod.ext ?_ ?_
    · rw [eA.coe_fst' hσA, eA.coe_fst' hyA]
      exact hσ
    · simp only [Φ, ψ, eA]
      have hσb : (e.toOpenPartialHomeomorph.symm (y.proj, g₀)).proj ∈ e.baseSet := by
        rw [hσ]
        exact hy
      rw [trivializationAt_mk_snd hσb, TotalSpace.eta, e.apply_symm_apply' hy, smul_inv_smul]
  refine ⟨ψ, hψ, hψ₀, ?_⟩
  filter_upwards [(FiberBundle.continuous_proj F _).continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds hb₀)] with y hy using hΦψ y hy

/-- **The associated bundle is the quotient of `P × F`.** The map `(p, v) ↦ [p, v]` from pairs of
points of the total space of `P` and of `F` onto the total space of the associated bundle is an
open quotient map. -/
theorem isOpenQuotientMap_totalSpaceMk_mk :
    IsOpenQuotientMap fun x : TotalSpace G P × F ↦
      (⟨x.1.proj, mk G x.1.2 x.2⟩ : TotalSpace F (AssociatedBundle G P F)) where
  surjective y := by
    -- Every fibre of `P` is nonempty, and any of its points gives every class over its base point.
    set q := (FiberBundle.homeomorphAt G P y.proj).symm 1
    obtain ⟨v, hv⟩ := (mk_bijective (F := F) q).2 y.2
    exact ⟨(⟨y.proj, q⟩, v), congrArg (TotalSpace.mk y.proj) hv⟩
  continuous := continuous_totalSpaceMk_mk G P F
  isOpenMap := isOpenMap_totalSpaceMk_mk G P F

/-- The total space of the associated bundle is homeomorphic to the quotient of `P × F` by the
orbit relation `(p, v) ∼ (p • g, g⁻¹ • v)`; the homeomorphism sends the class of `(p, v)` to
`[p, v]` (`TauCeti.AssociatedBundle.quotientHomeomorph_mk`). -/
noncomputable def quotientHomeomorph :
    Quotient (orbitRel G P F) ≃ₜ TotalSpace F (AssociatedBundle G P F) :=
  (Homeomorph.Quotient.congrRight (Setoid.ext_iff.1 orbitRel_eq_ker)).trans
    (Topology.IsQuotientMap.homeomorph (f := ⟨_, continuous_totalSpaceMk_mk G P F⟩)
      (isOpenQuotientMap_totalSpaceMk_mk G P F).isQuotientMap)

variable {G P F}

/-- The homeomorphism `quotientHomeomorph` sends the class of `(p, v)` to `[p, v]`. -/
@[simp]
theorem quotientHomeomorph_mk (x : TotalSpace G P × F) :
    quotientHomeomorph G P F (Quotient.mk _ x) = ⟨x.1.proj, mk G x.1.2 x.2⟩ :=
  (rfl)

end TauCeti.AssociatedBundle
