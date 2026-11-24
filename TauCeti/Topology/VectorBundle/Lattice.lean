/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.VectorBundle.Section

/-!
# Lattice families in vector bundles and their monodromy

Let `E` be a real vector bundle over `B` with finite-dimensional model fibre `F`, and let
`L b ≤ E b` be a family of additive subgroups. The points of the total space lying in these
subgroups form the space `{v : TotalSpace F E // v.2 ∈ L v.proj}`, and the bundle projection
restricts to a map `TauCeti.latticeProj F L` from it to `B`, whose fibre over `b` is `L b`
(`TauCeti.latticeProjFiberEquiv`).

Suppose that `L` is locally a family of full lattices spanned by a continuous frame: every point
of `B` has an open neighbourhood `U` with continuous sections `s₁, …, sₙ` over `U`, `n = dim F`,
linearly independent at every point of `U`, such that `L b = ℤ s₁(b) + ⋯ + ℤ sₙ(b)` for `b ∈ U`.
Then `latticeProj F L` is evenly covered over `U` with fibre `ℤⁿ`
(`TauCeti.isEvenlyCovered_latticeProj`): in a trivialization of `E` the frame becomes a
continuously varying basis of `F`, the coordinates of a lattice vector in this basis are integers,
and they depend continuously, hence locally constantly, on the lattice vector. So `latticeProj F L`
is a covering map (`TauCeti.isCoveringMap_latticeProj`).

Lifting paths in `B` to this covering transports lattice vectors along paths. The resulting
monodromy of Mathlib's `IsCoveringMap.monodromy` is additive, since the fibrewise sum of two lifts
of a path is again a lift: for a homotopy class of paths `γ` from `x` to `y` it is an isomorphism
of groups `L x ≃+ L y` (`TauCeti.latticeMonodromy`), and around loops at `x` it is a
representation of the fundamental group by automorphisms of the lattice `L x`
(`TauCeti.latticeMonodromyHom`). For a family of full lattices of rank `n`, `AddAut (L x)` is
`GL(n, ℤ)` after choosing a basis of `L x`: this is the **linear monodromy** of the lattice family.

A continuous section of `L` along a path is a lift of it, so monodromy carries its value at the
start to its value at the end (`TauCeti.latticeMonodromy_mk_of_continuousOn`). Consequently a
lattice family spanned by a global continuous frame has trivial monodromy
(`TauCeti.latticeMonodromyHom_eq_one`).

The motivating example is the period lattice `Λ ⊆ T*B` of a regular Lagrangian torus fibration,
which is locally spanned by the differentials of action coordinates; there `T*B/Λ` is the
associated torus bundle, and nontrivial monodromy obstructs global action coordinates.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 2 (the period lattice bundle and its monodromy).
-/

public section

noncomputable section

open Bundle Function Module Set Topology

namespace TauCeti

variable {B F : Type*} {E : B → Type*} [∀ b, AddCommGroup (E b)]

variable (F) in
/-- The bundle projection restricted to the points `v` of the total space whose fibre component
lies in the subgroup `L v.proj`. For a family of lattices locally spanned by continuous frames,
this is a covering map (`TauCeti.isCoveringMap_latticeProj`). -/
def latticeProj (L : ∀ b, AddSubgroup (E b)) :
    {v : TotalSpace F E // v.snd ∈ L v.proj} → B :=
  fun v ↦ v.val.proj

@[simp]
theorem latticeProj_apply (L : ∀ b, AddSubgroup (E b))
    (v : {v : TotalSpace F E // v.snd ∈ L v.proj}) : latticeProj F L v = v.val.proj :=
  (rfl)

variable (F) in
/-- The fibre of `latticeProj F L` over `b` is the subgroup `L b`. -/
def latticeProjFiberEquiv (L : ∀ b, AddSubgroup (E b)) (b : B) :
    latticeProj F L ⁻¹' {b} ≃ L b where
  toFun v := ⟨cast (congrArg E v.property) v.val.val.snd, by
    obtain ⟨⟨⟨x, w⟩, hw⟩, rfl⟩ := v
    exact hw⟩
  invFun w := ⟨⟨⟨b, w⟩, w.property⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨x, w⟩, hw⟩, rfl⟩
    rfl
  right_inv _ := rfl

@[simp]
theorem latticeProjFiberEquiv_mk (L : ∀ b, AddSubgroup (E b)) {b : B} (w : E b) (hw : w ∈ L b)
    (h : latticeProj F L ⟨⟨b, w⟩, hw⟩ ∈ ({b} : Set B)) :
    latticeProjFiberEquiv F L b ⟨⟨⟨b, w⟩, hw⟩, h⟩ = ⟨w, hw⟩ :=
  (rfl)

@[simp]
theorem latticeProjFiberEquiv_symm_apply (L : ∀ b, AddSubgroup (E b)) (b : B) (w : L b) :
    ((latticeProjFiberEquiv F L b).symm w : {v : TotalSpace F E // v.snd ∈ L v.proj}) =
      ⟨⟨b, w⟩, w.property⟩ :=
  (rfl)

/-- The fibrewise sum of two points of the total space over the same base point. -/
private def fiberAdd (u v : TotalSpace F E) (h : u.proj = v.proj) : TotalSpace F E :=
  ⟨u.proj, u.snd + cast (congrArg E h.symm) v.snd⟩

private theorem fiberAdd_mem {L : ∀ b, AddSubgroup (E b)}
    {u v : TotalSpace F E} (h : u.proj = v.proj) (hu : u.snd ∈ L u.proj) (hv : v.snd ∈ L v.proj) :
    (fiberAdd u v h).snd ∈ L (fiberAdd u v h).proj := by
  obtain ⟨x, a⟩ := u
  obtain ⟨y, c⟩ := v
  obtain rfl : x = y := h
  exact add_mem hu hv

private theorem fiberAdd_congr {u u' v v' : TotalSpace F E} (hu : u = u') (hv : v = v')
    (h : u.proj = v.proj) (h' : u'.proj = v'.proj) : fiberAdd u v h = fiberAdd u' v' h' := by
  subst hu hv
  rfl

/-- On the fibre over `b`, the fibrewise sum is the addition of `L b`. -/
private theorem latticeProjFiberEquiv_fiberAdd {L : ∀ b, AddSubgroup (E b)} {b : B}
    (u v : latticeProj F L ⁻¹' {b}) (h : u.val.val.proj = v.val.val.proj) :
    latticeProjFiberEquiv F L b ⟨⟨fiberAdd u.val.val v.val.val h,
        fiberAdd_mem h u.val.property v.val.property⟩, u.property⟩ =
      latticeProjFiberEquiv F L b u + latticeProjFiberEquiv F L b v := by
  obtain ⟨⟨⟨x, a⟩, ha⟩, rfl⟩ := u
  obtain ⟨⟨⟨y, c⟩, hc⟩, hy⟩ := v
  obtain rfl : y = x := hy
  rfl

/-- A point of the fibre over `b` which is the value at some `z` of a section `s` corresponds to
`s b ∈ L b`. -/
theorem latticeProjFiberEquiv_eq_of_val_eq {L : ∀ b, AddSubgroup (E b)} {s : ∀ b, E b}
    {b z : B} (v : latticeProj F L ⁻¹' {b}) (hv : v.val.val = ⟨z, s z⟩) (hb : s b ∈ L b) :
    latticeProjFiberEquiv F L b v = ⟨s b, hb⟩ := by
  obtain ⟨⟨⟨x, w⟩, hw⟩, rfl⟩ := v
  obtain ⟨rfl, h⟩ := TotalSpace.mk.inj hv
  cases h
  rfl

section Covering

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] in
variable (F) in
/-- The projection of a lattice family to the base is continuous. -/
theorem continuous_latticeProj (L : ∀ b, AddSubgroup (E b)) : Continuous (latticeProj F L) :=
  (FiberBundle.continuous_proj F E).comp continuous_subtypeVal

variable [VectorBundle ℝ F E] [FiniteDimensional ℝ F]

/-- **Integer coordinates in a continuous frame.** Over the part of an open set `U` where a
continuous frame spans `L`, lying in the base of the trivialization at `b₀`, the integer
coordinates of lattice vectors in the frame are unique and depend continuously on the lattice
vector. In the trivialization the frame is a continuously varying basis of `F`, whose real
coordinate maps vary continuously. -/
private theorem exists_continuous_intCoord {L : ∀ b, AddSubgroup (E b)} {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = finrank ℝ F) {s : ι → ∀ b, E b} {U : Set B}
    (hs : ∀ i, ContinuousOn (fun b ↦ TotalSpace.mk' F b (s i b)) U)
    (hli : ∀ b ∈ U, LinearIndependent ℝ fun i ↦ s i b)
    (hLs : ∀ b ∈ U, L b = AddSubgroup.closure (range fun i ↦ s i b)) (b₀ : B) :
    ∃ k : latticeProj F L ⁻¹' (U ∩ (trivializationAt F E b₀).baseSet) → ι → ℤ, Continuous k ∧
      (∀ v, v.val.val.snd = ∑ i, k v i • s i v.val.val.proj) ∧
      ∀ v (n : ι → ℤ), v.val.val.snd = ∑ i, n i • s i v.val.val.proj → k v = n := by
  set e := trivializationAt F E b₀
  set U' := U ∩ e.baseSet
  -- In the trivialization `e`, the frame is a basis `W b` of `F` at every point of `U'`, and its
  -- coordinate maps vary continuously.
  let w : U' → ι → F := fun b i ↦ (e ⟨b, s i b⟩).2
  have hw (b : U') : LinearIndependent ℝ (w b) := by
    simpa [w, Function.comp_def] using (hli b b.property.1).map'
      (e.linearEquivAt ℝ b b.property.2).toLinearMap (e.linearEquivAt ℝ b b.property.2).ker
  let W : U' → Basis ι ℝ F := fun b ↦ basisOfLinearIndependentOfCardEqFinrank' (w b) (hw b) hι
  have hWc : Continuous fun b ↦ ((W b).equivFunL : F →L[ℝ] ι → ℝ) := by
    refine Basis.continuous_equivFunL_of_continuous fun i ↦ ?_
    simp only [W, coe_basisOfLinearIndependentOfCardEqFinrank', w]
    exact ((e.continuousOn_section_iff inter_subset_right).1
      ((hs i).mono inter_subset_left)).comp_continuous continuous_subtypeVal Subtype.prop
  -- The coordinates of an integer combination of the frame are its integer coefficients.
  have hcoord₀ (b : U') (n : ι → ℤ) :
      (W b).equivFun ((e ⟨b, ∑ i, n i • s i b⟩).2) = fun i ↦ (n i : ℝ) := by
    rw [← e.linearEquivAt_apply (R := ℝ) b b.property.2, map_sum]
    simp_rw [map_zsmul, e.linearEquivAt_apply, ← Int.cast_smul_eq_zsmul ℝ]
    have : ∑ i, (n i : ℝ) • (e ⟨b, s i b⟩).2 = (W b).equivFun.symm fun i ↦ (n i : ℝ) := by
      simp [Basis.equivFun_symm_apply, W, w]
    rw [this, LinearEquiv.apply_symm_apply]
  have hcoord (v : latticeProj F L ⁻¹' U') (n : ι → ℤ)
      (hn : v.val.val.snd = ∑ i, n i • s i v.val.val.proj) :
      (W ⟨_, v.property⟩).equivFun ((e v.val.val).2) = fun i ↦ (n i : ℝ) := by
    exact (congrArg (fun y ↦ (W ⟨_, v.property⟩).equivFun (e ⟨v.val.val.proj, y⟩).2) hn).trans
      (hcoord₀ ⟨_, v.property⟩ n)
  -- Every point of the lattice over `U'` is an integer combination of the frame.
  have hex (v : latticeProj F L ⁻¹' U') :
      ∃ n : ι → ℤ, v.val.val.snd = ∑ i, n i • s i v.val.val.proj := by
    have h := v.val.property
    rwa [hLs v.val.val.proj v.property.1, AddSubgroup.mem_closure_range_iff_of_fintype] at h
  choose k hk using hex
  refine ⟨k, ?_, hk, fun v n hn ↦ funext fun i ↦ Int.cast_injective (α := ℝ)
    (congrFun ((hcoord v (k v) (hk v)).symm.trans (hcoord v n hn)) i)⟩
  -- The real coordinates are continuous, and they are the integer coordinates.
  refine (IsEmbedding.piMap fun _ : ι ↦
    Int.isClosedEmbedding_coe_real.isEmbedding).continuous_iff.2 ?_
  have he : Continuous fun v : latticeProj F L ⁻¹' U' ↦ (e v.val.val).2 :=
    continuous_snd.comp <| e.continuousOn.comp_continuous
      (continuous_subtypeVal.comp continuous_subtypeVal) fun v ↦ e.mem_source.2 v.property.2
  exact ((hWc.comp (((continuous_latticeProj F L).comp continuous_subtypeVal).subtype_mk
    fun v ↦ v.property)).clm_apply he).congr fun v ↦ hcoord v _ (hk v)

/-- **A lattice family spanned by a continuous frame is evenly covered.** Let `sᵢ`, `i ∈ ι`, with
`ι` of cardinality `dim F`, be sections of `E` continuous on an open set `U`, linearly independent
at every point of `U`, and spanning `L b` over `ℤ` at every `b ∈ U`. Then every point of `U` is
evenly covered by `latticeProj F L`, with fibre `ℤ^ι`: the integer coordinates in the frame
identify the part of the lattice bundle over a neighbourhood with the product of that
neighbourhood and `ℤ^ι`. -/
theorem isEvenlyCovered_latticeProj {L : ∀ b, AddSubgroup (E b)} {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = finrank ℝ F) {s : ι → ∀ b, E b} {U : Set B} (hU : IsOpen U)
    (hs : ∀ i, ContinuousOn (fun b ↦ TotalSpace.mk' F b (s i b)) U)
    (hli : ∀ b ∈ U, LinearIndependent ℝ fun i ↦ s i b)
    (hLs : ∀ b ∈ U, L b = AddSubgroup.closure (range fun i ↦ s i b)) {b₀ : B} (hb₀ : b₀ ∈ U) :
    IsEvenlyCovered (latticeProj F L) b₀ (ι → ℤ) := by
  obtain ⟨k, hkcont, hk, hkuniq⟩ := exists_continuous_intCoord hι hs hli hLs b₀
  have hU' : IsOpen (U ∩ (trivializationAt F E b₀).baseSet) :=
    hU.inter (trivializationAt F E b₀).open_baseSet
  have hmem (b : ↥(U ∩ (trivializationAt F E b₀).baseSet)) (n : ι → ℤ) :
      ∑ i, n i • s i b ∈ L b := by
    rw [hLs b b.property.1]
    exact sum_mem fun i _ ↦
      zsmul_mem (AddSubgroup.subset_closure (mem_range_self (f := fun i ↦ s i b) i)) _
  refine ⟨inferInstance, U ∩ (trivializationAt F E b₀).baseSet,
    ⟨hb₀, mem_baseSet_trivializationAt F E b₀⟩, hU',
    hU'.preimage (continuous_latticeProj F L), ⟨
    { toFun v := (⟨_, v.property⟩, k v)
      invFun p := ⟨⟨⟨p.1, ∑ i, p.2 i • s i p.1⟩, hmem p.1 p.2⟩, p.1.property⟩
      left_inv v := ?_
      right_inv p := Prod.ext rfl
        (hkuniq ⟨⟨⟨p.1, ∑ i, p.2 i • s i p.1⟩, hmem p.1 p.2⟩, p.1.property⟩ p.2 rfl)
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun v ↦ rfl⟩⟩
  · obtain ⟨⟨⟨b, x⟩, hx⟩, hb⟩ := v
    exact Subtype.ext <| Subtype.ext <| congrArg (TotalSpace.mk' F b) (hk _).symm
  · exact (((continuous_latticeProj F L).comp continuous_subtypeVal).subtype_mk _).prodMk hkcont
  · refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    refine continuous_prod_of_discrete_right.2 fun n ↦ ?_
    refine ContinuousOn.comp_continuous (f := Subtype.val)
      (g := fun b ↦ TotalSpace.mk' F b (∑ i, n i • s i b)) (fun b hb ↦ ?_) continuous_subtypeVal
      Subtype.prop
    simp_rw [← Int.cast_smul_eq_zsmul ℝ]
    exact (ContinuousAt.sum_section ℝ (I := Finset.univ) fun i _ ↦ continuousAt_const.smul_section
      ((hs i).continuousAt (hU.mem_nhds hb.1))).continuousWithinAt

/-- **A lattice family locally spanned by continuous frames is a covering space.** If every point
of `B` has an open neighbourhood `U` with sections `sᵢ`, `i ∈ ι`, with `ι` of cardinality
`dim F`, continuous on `U`,
linearly independent at every point of `U`, and spanning `L b` over `ℤ` at every `b ∈ U`, then
the projection `latticeProj F L` of the lattice bundle to `B` is a covering map. -/
theorem isCoveringMap_latticeProj (L : ∀ b, AddSubgroup (E b)) {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = finrank ℝ F)
    (hL : ∀ b₀, ∃ (s : ι → ∀ b, E b) (U : Set B), IsOpen U ∧ b₀ ∈ U ∧
      (∀ i, ContinuousOn (fun b ↦ TotalSpace.mk' F b (s i b)) U) ∧
      ∀ b ∈ U, LinearIndependent ℝ (fun i ↦ s i b) ∧
        L b = AddSubgroup.closure (range fun i ↦ s i b)) :
    IsCoveringMap (latticeProj F L) := fun b₀ ↦ by
  obtain ⟨s, U, hU, hb₀, hs, h⟩ := hL b₀
  exact (isEvenlyCovered_latticeProj hι hU hs (fun b hb ↦ (h b hb).1) (fun b hb ↦ (h b hb).2)
    hb₀).to_isEvenlyCovered_preimage

end Covering

section Monodromy

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] {L : ∀ b, AddSubgroup (E b)} (hL : IsCoveringMap (latticeProj F L))

include hL in
/-- The fibrewise sum of two lifts of a path is the lift of the path starting at the sum. -/
private theorem latticeProjFiberEquiv_monodromy_add {x y : B} (γ : Path x y) (a c : L x) :
    latticeProjFiberEquiv F L y
        (hL.monodromy (.mk γ) ((latticeProjFiberEquiv F L x).symm (a + c))) =
      latticeProjFiberEquiv F L y (hL.monodromy (.mk γ) ((latticeProjFiberEquiv F L x).symm a)) +
        latticeProjFiberEquiv F L y
          (hL.monodromy (.mk γ) ((latticeProjFiberEquiv F L x).symm c)) := by
  set ea := (latticeProjFiberEquiv F L x).symm a
  set ec := (latticeProjFiberEquiv F L x).symm c
  set Γa := hL.liftPath γ ea (γ.source.trans ea.property.symm)
  set Γc := hL.liftPath γ ec (γ.source.trans ec.property.symm)
  have hpa : latticeProj F L ∘ Γa = γ := hL.liftPath_lifts ..
  have hac (t) : (Γa t).val.proj = (Γc t).val.proj :=
    congrFun (hpa.trans (hL.liftPath_lifts ..).symm) t
  -- The fibrewise sum of the two lifts is again a lift of `γ`.
  let Γ : C(unitInterval, {v : TotalSpace F E // v.snd ∈ L v.proj}) :=
    ⟨fun t ↦ ⟨fiberAdd (Γa t).val (Γc t).val (hac t),
      fiberAdd_mem _ (Γa t).property (Γc t).property⟩, by
      refine Continuous.subtype_mk ?_ _
      refine Continuous.add_totalSpace (b := fun t ↦ (Γa t).val.proj) ℝ
        (s := fun t ↦ (Γa t).val.snd) (t := fun t ↦ cast (congrArg E (hac t).symm) (Γc t).val.snd)
        (continuous_subtypeVal.comp Γa.continuous) ?_
      exact (continuous_subtypeVal.comp Γc.continuous).congr fun t ↦
        (TotalSpace.mk_cast (hac t).symm _).symm⟩
  -- It starts at the sum of the starting points.
  have hΓ0 : Γ 0 = ((latticeProjFiberEquiv F L x).symm (a + c) : _) := by
    have h0 : Γ 0 = ⟨fiberAdd ea.val.val ec.val.val (ea.property.trans ec.property.symm),
        fiberAdd_mem _ ea.val.property ec.val.property⟩ :=
      Subtype.ext (fiberAdd_congr (congrArg Subtype.val (hL.liftPath_zero ..))
        (congrArg Subtype.val (hL.liftPath_zero ..)) (hac 0) (ea.property.trans ec.property.symm))
    have h := latticeProjFiberEquiv_fiberAdd ea ec (ea.property.trans ec.property.symm)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← Equiv.eq_symm_apply] at h
    rw [h0]
    exact congrArg Subtype.val h
  -- So it ends at the monodromy of the sum, which is the sum of the monodromies.
  set ma := hL.monodromy (.mk γ) ea
  set mc := hL.monodromy (.mk γ) ec
  have h1 : hL.monodromy (.mk γ) ((latticeProjFiberEquiv F L x).symm (a + c)) =
      ⟨⟨fiberAdd ma.val.val mc.val.val (ma.property.trans mc.property.symm),
        fiberAdd_mem _ ma.val.property mc.val.property⟩, ma.property⟩ :=
    Subtype.ext ((hL.monodromy_eq_apply_one (Γ := Γ) hpa hΓ0).trans (Subtype.ext
      (fiberAdd_congr (congrArg Subtype.val (hL.coe_monodromy_mk ..)).symm
        (congrArg Subtype.val (hL.coe_monodromy_mk ..)).symm (hac 1)
        (ma.property.trans mc.property.symm))))
  rw [h1]
  exact latticeProjFiberEquiv_fiberAdd ma mc _

/-- **Monodromy of a lattice family.** Transport along a homotopy class of paths `γ` from `x` to
`y`, by lifting `γ` to the covering `latticeProj F L`, is an isomorphism of groups `L x ≃+ L y`:
it is additive since the fibrewise sum of two lifts of `γ` is again a lift. -/
def latticeMonodromy {x y : B} (γ : Path.Homotopic.Quotient x y) : L x ≃+ L y where
  toEquiv := ((latticeProjFiberEquiv F L x).symm.trans
    (Equiv.ofBijective _ (hL.monodromy_bijective γ))).trans (latticeProjFiberEquiv F L y)
  map_add' a c := by
    obtain ⟨γ⟩ := γ
    exact latticeProjFiberEquiv_monodromy_add hL γ a c

theorem latticeMonodromy_apply {x y : B} (γ : Path.Homotopic.Quotient x y) (a : L x) :
    latticeMonodromy hL γ a =
      latticeProjFiberEquiv F L y (hL.monodromy γ ((latticeProjFiberEquiv F L x).symm a)) :=
  (rfl)

@[simp]
theorem latticeMonodromy_refl (x : B) (a : L x) : latticeMonodromy hL (.refl x) a = a := by
  rw [latticeMonodromy_apply, hL.monodromy_refl, id, Equiv.apply_symm_apply]

theorem latticeMonodromy_trans {x y z : B} (γ : Path.Homotopic.Quotient x y)
    (γ' : Path.Homotopic.Quotient y z) (a : L x) :
    latticeMonodromy hL (γ.trans γ') a = latticeMonodromy hL γ' (latticeMonodromy hL γ a) := by
  simp only [latticeMonodromy_apply, hL.monodromy_trans_apply, Equiv.symm_apply_apply]

/-- **The linear monodromy representation of a lattice family.** Transport around loops at `x`
is a representation of the fundamental group of `B` at `x` on the lattice `L x`, by
`ℤ`-linear automorphisms. For a lattice of rank `n`, a basis of `L x` identifies its target with
`GL(n, ℤ)`. -/
def latticeMonodromyHom (x : B) : FundamentalGroup B x →* LinearMap.GeneralLinearGroup ℤ (L x) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ (L x)).symm.toMonoidHom.comp
    { toFun γ := (latticeMonodromy hL γ.asHom).toIntLinearEquiv
      map_one' := LinearEquiv.ext fun a ↦ latticeMonodromy_refl hL x a
      map_mul' γ γ' := LinearEquiv.ext fun a ↦ latticeMonodromy_trans hL γ'.asHom γ.asHom a }

@[simp]
theorem latticeMonodromyHom_apply (x : B) (γ : FundamentalGroup B x) (a : L x) :
    (latticeMonodromyHom hL x γ : L x →ₗ[ℤ] L x) a = latticeMonodromy hL γ.asHom a := by
  rw [← LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
  simp [latticeMonodromyHom]

/-- **Monodromy follows continuous sections.** If a section `s` of `E` is continuous on a set `U`
and takes values in `L` there, then transport along a path `γ` in `U` carries `s` at the start of
`γ` to `s` at its end: `t ↦ s (γ t)` is the lift of `γ`. -/
theorem latticeMonodromy_mk_of_continuousOn {s : ∀ b, E b} {U : Set B}
    (hs : ContinuousOn (fun b ↦ TotalSpace.mk' F b (s b)) U) (hsL : ∀ b ∈ U, s b ∈ L b)
    {x y : B} (γ : Path x y) (hγ : ∀ t, γ t ∈ U) :
    latticeMonodromy hL (.mk γ) ⟨s x, hsL x (γ.source ▸ hγ 0)⟩ =
      ⟨s y, hsL y (γ.target ▸ hγ 1)⟩ := by
  let Γ : C(unitInterval, {v : TotalSpace F E // v.snd ∈ L v.proj}) :=
    ⟨fun t ↦ ⟨⟨γ t, s (γ t)⟩, hsL _ (hγ t)⟩, (hs.comp_continuous γ.continuous hγ).subtype_mk _⟩
  have hΓ0 : Γ 0 = ((latticeProjFiberEquiv F L x).symm ⟨s x, hsL x (γ.source ▸ hγ 0)⟩ : _) := by
    rw [latticeProjFiberEquiv_symm_apply]
    exact Subtype.ext (congrArg (fun z ↦ TotalSpace.mk' F z (s z)) γ.source)
  rw [latticeMonodromy_apply]
  exact latticeProjFiberEquiv_eq_of_val_eq _
    (congrArg Subtype.val (hL.monodromy_eq_apply_one (Γ := Γ) rfl hΓ0)) _

/-- **A lattice family spanned by a global continuous frame has trivial monodromy.** -/
theorem latticeMonodromyHom_eq_one {ι : Type*} [Finite ι] {s : ι → ∀ b, E b}
    (hs : ∀ i, Continuous fun b ↦ TotalSpace.mk' F b (s i b))
    (hLs : ∀ b, L b = AddSubgroup.closure (range fun i ↦ s i b)) (x : B) :
    latticeMonodromyHom hL x = 1 := by
  have := Fintype.ofFinite ι
  have hsL (i : ι) (b : B) : s i b ∈ L b := by
    rw [hLs b]
    exact AddSubgroup.subset_closure (mem_range_self (f := fun i ↦ s i b) i)
  refine MonoidHom.ext fun γ ↦ Units.ext (LinearMap.ext fun a ↦ ?_)
  rw [latticeMonodromyHom_apply, MonoidHom.one_apply, Units.val_one, Module.End.one_eq_id,
    LinearMap.id_apply]
  obtain ⟨k, hk⟩ := (AddSubgroup.mem_closure_range_iff_of_fintype (f := fun i ↦ s i x)).1
    ((hLs x).le a.property)
  have ha : a = ∑ i, k i • (⟨s i x, hsL i x⟩ : L x) := Subtype.ext (by simpa using hk)
  generalize γ.asHom = q
  obtain ⟨q⟩ := q
  calc latticeMonodromy hL (.mk q) a
      = latticeMonodromy hL (.mk q) (∑ i, k i • (⟨s i x, hsL i x⟩ : L x)) := congrArg _ ha
    _ = ∑ i, k i • (⟨s i x, hsL i x⟩ : L x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_zsmul, latticeMonodromy_mk_of_continuousOn hL (hs i).continuousOn
        (fun b _ ↦ hsL i b) q fun _ ↦ mem_univ _]
    _ = a := ha.symm

end Monodromy

end TauCeti
