/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus
public import TauCeti.Geometry.Manifold.Diffeomorph.Interval
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# Interval charts of the smooth mapping torus

Let `φ` be a `C^n` diffeomorphism of a locally compact Hausdorff manifold `M` and
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` its smooth mapping torus
(`TauCeti.SmoothMappingTorus φ`), with projection `p : Y_φ → ℝ / ℤ`, `[t, x] ↦ [t]`. Over an arc of
the circle of length at most one, the mapping torus is a product: for an open interval `(a, b)` with
`b ≤ a + 1`, the quotient map `(t, x) ↦ [t, x]` is injective on `(a, b) × M`, so it identifies
`(a, b) × M` smoothly with the open set `p⁻¹ [(a, b)]` of `Y_φ`.

The inverse identification `TauCeti.SmoothMappingTorus.intervalChart φ a b`, from `p⁻¹ [(a, b)]`
onto `(a, b) × M`, is a `C^n` partial diffeomorphism with values in the manifold `ℝ × M`. It sends a
point `[t, x]` to its unique representative `(t + k, φ ^ (-k) x)` with real coordinate in `(a, b)`.
So two
interval charts differ on their overlap by a shift of the real coordinate by an integer `k`
together with the fibre transition `φ ^ (-k)`, and their real coordinates lift the projection `p`.
Followed by any chart `e` of the maximal atlas of `ℝ × M`, for instance by the identity of an
interval times a chart of `M`, an interval chart is a chart of the maximal atlas of `Y_φ`: this is
`(intervalChart φ a b hab).trans_mem_maximalAtlas he`, an instance of the general
`PartialDiffeomorph.trans_mem_maximalAtlas`.

## Main definitions

* `TauCeti.SmoothMappingTorus.intervalCutOpens φ a b`: the open region over the image of `(a,b)`
  in the circle, without a nonemptiness or interval-length assumption.
* `TauCeti.SmoothMappingTorus.intervalCutDiffeomorph φ hab`: the bundled comparison from
  `M × (a,b)` to this cut for an interval of length at most one, including an empty fibre.
* `TauCeti.SmoothMappingTorus.intervalChart φ a b hab`: for `b ≤ a + 1`, the `C^n` partial
  diffeomorphism from `p⁻¹ [(a, b)]` onto `(a, b) × M` inverse to `(t, x) ↦ [t, x]`.

## Main results

* `TauCeti.SmoothMappingTorus.injOn_uncurry_mk_Ioo_prod`: `(t, x) ↦ [t, x]` is injective on
  `(a, b) × M` when `b ≤ a + 1`.
* `TauCeti.SmoothMappingTorus.image_uncurry_mk_Ioo_prod`: its image is `p⁻¹ [(a, b)]`.
* `TauCeti.SmoothMappingTorus.intervalChart_mk_of_add_intCast_mem`: the interval chart sends
  `[t, x]` to `(t + k, φ ^ (-k) x)` when `t + k ∈ (a, b)`; this is the integer-shift transition
  between interval charts.
* `TauCeti.SmoothMappingTorus.coe_intervalChart_fst`: the real coordinate of the interval chart
  lifts the projection to the circle.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  (φ : M ≃ₘ^n⟮I, I⟯ M) {a b : ℝ}

/-- The quotient map `(t, x) ↦ [t, x]` is injective on `(a, b) × M` when the interval `(a, b)` has
length at most one. -/
theorem injOn_uncurry_mk_Ioo_prod (hab : b ≤ a + 1) :
    InjOn (uncurry (mk φ)) (Ioo a b ×ˢ univ) := by
  rintro ⟨t, x⟩ ⟨ht, -⟩ ⟨s, y⟩ ⟨hs, -⟩ h
  have hp : (t : UnitAddCircle) = s := by
    simpa only [uncurry_apply_pair, proj_mk] using congrArg (proj φ) h
  obtain rfl : t = s := (AddCircle.coe_eq_coe_iff_of_mem_Ico ⟨ht.1.le, ht.2.trans_le hab⟩
    ⟨hs.1.le, hs.2.trans_le hab⟩).1 hp
  exact Prod.ext rfl (mk_injective φ t h)

/-- The image of `(a, b) × M` under the quotient map `(t, x) ↦ [t, x]` is the preimage under the
projection to the circle of the image of `(a, b)`. -/
theorem image_uncurry_mk_Ioo_prod :
    uncurry (mk φ) '' (Ioo a b ×ˢ univ) =
      proj φ ⁻¹' (((↑) : ℝ → UnitAddCircle) '' Ioo a b) := by
  refine Subset.antisymm ?_ fun z ⟨t, ht, hz⟩ ↦ ?_
  · rintro _ ⟨⟨t, x⟩, ⟨ht, -⟩, rfl⟩
    exact ⟨t, ht, (proj_mk φ t x).symm⟩
  · obtain ⟨x, rfl⟩ : z ∈ range (mk φ t) := by rw [range_mk]; exact hz.symm
    exact ⟨(t, x), ⟨ht, mem_univ x⟩, rfl⟩

/-- The open mapping-torus region whose circle coordinate has a representative in `(a,b)`.
No interval-length, nonemptiness or manifold-regularity assumption is needed for this open set. -/
def intervalCutOpens (a b : ℝ) : TopologicalSpace.Opens (SmoothMappingTorus φ) :=
  ⟨proj φ ⁻¹' (((↑) : ℝ → UnitAddCircle) '' Ioo a b),
    (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).preimage (continuous_proj φ)⟩

/-- A point belongs to the interval cut precisely when its circle coordinate has a
representative in `(a,b)`. -/
@[simp]
theorem mem_intervalCutOpens (x : SmoothMappingTorus φ) :
    x ∈ intervalCutOpens φ a b ↔
      proj φ x ∈ (((↑) : ℝ → UnitAddCircle) '' Ioo a b) := (Iff.rfl)

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [Nonempty M]

/-- The interval chart of the mapping torus over the interval `(a, b)`, of length at most one: the
`C^n` partial diffeomorphism from `p⁻¹ [(a, b)]` onto `(a, b) × M` inverse to `(t, x) ↦ [t, x]`. It
sends `[t, x]` to its unique representative with real coordinate in `(a, b)`
(`TauCeti.SmoothMappingTorus.intervalChart_mk_of_add_intCast_mem`). -/
def intervalChart (a b : ℝ) (hab : b ≤ a + 1) :
    PartialDiffeomorph (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (SmoothMappingTorus φ) (ℝ × M) n :=
  ((isLocalDiffeomorph_uncurry_mk φ).isLocalDiffeomorphOn _).partialDiffeomorphOfInjOn
    (isOpen_Ioo.prod isOpen_univ) (injOn_uncurry_mk_Ioo_prod φ hab) |>.symm

variable (hab : b ≤ a + 1)

/-- The source of the interval chart over `(a, b)` is the preimage of `[(a, b)]` under the
projection to the circle. -/
@[simp]
theorem intervalChart_source :
    (intervalChart φ a b hab).source = proj φ ⁻¹' (((↑) : ℝ → UnitAddCircle) '' Ioo a b) := by
  rw [← image_uncurry_mk_Ioo_prod φ]
  simp [intervalChart]

/-- The target of the interval chart over `(a, b)` is `(a, b) × M`. -/
@[simp]
theorem intervalChart_target : (intervalChart φ a b hab).target = Ioo a b ×ˢ univ := by
  simp [intervalChart]

/-- The inverse of the interval chart is the quotient map `(t, x) ↦ [t, x]`. -/
@[simp]
theorem coe_intervalChart_symm :
    ⇑(intervalChart φ a b hab).toPartialEquiv.symm = uncurry (mk φ) := by
  simp [intervalChart]

/-- The interval chart over `(a, b)` sends `[t, x]`, for `t ∈ (a, b)`, to `(t, x)`. -/
@[simp]
theorem intervalChart_mk {t : ℝ} (ht : t ∈ Ioo a b) (x : M) :
    intervalChart φ a b hab (mk φ t x) = (t, x) := by
  have hs : (intervalChart φ a b hab).symm (t, x) = mk φ t x :=
    congrFun (coe_intervalChart_symm φ hab) (t, x)
  rw [← hs]
  exact (intervalChart φ a b hab).right_inv (x := (t, x)) (by simpa using ht)

/-- The interval chart over `(a, b)` sends `[t, x]` to `(t + k, φ ^ (-k) x)` whenever
`t + k ∈ (a, b)`. So on the overlap of two interval charts, the transition shifts the real
coordinate by an integer `k` and moves the fibre coordinate by `φ ^ (-k)`. -/
theorem intervalChart_mk_of_add_intCast_mem {t : ℝ} {k : ℤ} (ht : t + k ∈ Ioo a b) (x : M) :
    intervalChart φ a b hab (mk φ t x) = (t + k, (φ ^ (-k)) x) := by
  rw [← intervalChart_mk φ hab ht, mk_add_intCast, zpow_neg]
  -- `φ ^ k` undoes `(φ ^ k)⁻¹`.
  exact congrArg _ (congrArg _ (smul_inv_smul (φ ^ k) x).symm)

/-- The quotient map `(t, x) ↦ [t, x]` inverts the interval chart on its source. -/
theorem mk_intervalChart {z : SmoothMappingTorus φ} (hz : z ∈ (intervalChart φ a b hab).source) :
    mk φ (intervalChart φ a b hab z).1 (intervalChart φ a b hab z).2 = z := by
  have hs : (intervalChart φ a b hab).symm (intervalChart φ a b hab z) =
      mk φ (intervalChart φ a b hab z).1 (intervalChart φ a b hab z).2 :=
    congrFun (coe_intervalChart_symm φ hab) (intervalChart φ a b hab z)
  exact hs.symm.trans ((intervalChart φ a b hab).left_inv hz)

/-- The real coordinate of the interval chart lifts the projection to the circle. -/
theorem coe_intervalChart_fst {z : SmoothMappingTorus φ}
    (hz : z ∈ (intervalChart φ a b hab).source) :
    ((intervalChart φ a b hab z).1 : UnitAddCircle) = proj φ z := by
  conv_rhs => rw [← mk_intervalChart φ hab hz]
  rw [proj_mk]

omit [Nonempty M] in
private theorem intervalCutMap_local :
    IsLocalDiffeomorph (I.prod 𝓘(ℝ)) (𝓘(ℝ).prod I) n
      (fun p : prodIooOpens M a b ↦ mk φ p.val.2 p.val.1) := fun p ↦
  (TauCeti.isLocalDiffeomorph_subtype_val (I := I.prod 𝓘(ℝ)) (n := n) p).comp
    (hg := ((Diffeomorph.prodComm I 𝓘(ℝ) M ℝ n).isLocalDiffeomorph _).comp
      (hg := isLocalDiffeomorph_uncurry_mk φ _))

omit [Nonempty M] [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] in
private theorem intervalCutMap_injective (hab : b ≤ a + 1) :
    Injective (fun p : prodIooOpens M a b ↦ mk φ p.val.2 p.val.1) := by
  intro p q hpq
  have hp : (p.val.2, p.val.1) ∈ Ioo a b ×ˢ univ :=
    ⟨mem_prodIooOpens.1 p.property, trivial⟩
  have hq : (q.val.2, q.val.1) ∈ Ioo a b ×ˢ univ :=
    ⟨mem_prodIooOpens.1 q.property, trivial⟩
  have h := injOn_uncurry_mk_Ioo_prod φ hab hp hq hpq
  exact Subtype.ext (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))

omit [Nonempty M] [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] in
private theorem range_intervalCutMap :
    range (fun p : prodIooOpens M a b ↦ mk φ p.val.2 p.val.1) = intervalCutOpens φ a b := by
  -- The open cut stores precisely this preimage; only its `Opens` wrapper is unfolded.
  change range (fun p : prodIooOpens M a b ↦ mk φ p.val.2 p.val.1) =
    proj φ ⁻¹' (((↑) : ℝ → UnitAddCircle) '' Ioo a b)
  rw [← image_uncurry_mk_Ioo_prod φ]
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(p.val.2, p.val.1), ⟨mem_prodIooOpens.1 p.property, trivial⟩, rfl⟩
  · rintro ⟨⟨t, x⟩, ⟨ht, -⟩, rfl⟩
    exact ⟨⟨(x, t), mem_prodIooOpens.2 ht⟩, rfl⟩

omit [Nonempty M] in
/-- The product cylinder `M × (a,b)` maps diffeomorphically to the native interval cut
by sending `(x,t)` to the quotient class `[t,x]`. The fibre may be empty. -/
def intervalCutDiffeomorph :
    prodIooOpens M a b ≃ₘ^n⟮I.prod 𝓘(ℝ), 𝓘(ℝ).prod I⟯ intervalCutOpens φ a b :=
  (intervalCutMap_local φ).diffeomorphOfInjectiveOfRangeEq
    (intervalCutMap_injective φ hab) (range_intervalCutMap φ)

omit [Nonempty M] in
/-- The bundled interval-cut comparison is the native quotient map on its product cylinder. -/
@[simp]
theorem intervalCutDiffeomorph_apply_coe (p : prodIooOpens M a b) :
    (intervalCutDiffeomorph φ hab p : SmoothMappingTorus φ) = mk φ p.val.2 p.val.1 := by
  simp only [intervalCutDiffeomorph,
    IsLocalDiffeomorph.diffeomorphOfInjectiveOfRangeEq_apply_coe]

/-- The inverse bundled comparison reads the interval chart and swaps its real and fibre
coordinates back to the cylinder order. -/
@[simp]
theorem intervalCutDiffeomorph_symm_apply_coe (x : intervalCutOpens φ a b) :
    ((intervalCutDiffeomorph φ hab).symm x : M × ℝ) =
      ((intervalChart φ a b hab x).2, (intervalChart φ a b hab x).1) := by
  let p := (intervalCutDiffeomorph φ hab).symm x
  have hclass : mk φ p.val.2 p.val.1 = (x : SmoothMappingTorus φ) := by
    rw [← intervalCutDiffeomorph_apply_coe φ hab p]
    exact congrArg Subtype.val ((intervalCutDiffeomorph φ hab).apply_symm_apply x)
  have h := intervalChart_mk φ hab ((mem_prodIooOpens.1 p.property)) p.val.1
  rw [hclass] at h
  exact Prod.ext (congrArg Prod.snd h).symm (congrArg Prod.fst h).symm

end SmoothMappingTorus

end TauCeti
