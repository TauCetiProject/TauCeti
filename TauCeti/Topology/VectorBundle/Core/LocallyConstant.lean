/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Gluing point-indexed vector-bundle cores along a locally constant partition

Given a locally constant function `c : LocallyConstant B S` on a topological space `B` and a family
of point-indexed vector-bundle cores `Z s` with common model fibre `F` on the clopen fibres
`{b : B // c b = s}`, `VectorBundleCore.ofLocallyConstant` assembles them into a single
point-indexed `VectorBundleCore 𝕜 B F B` over `B`. Neither separation or compactness on `B`, nor a
topology, decidable equality, or countability on `S`, nor finite-dimensionality of `F` is assumed.

`VectorBundleCore.ofLocallyConstantHomeomorph` identifies the disjoint union
`Σ s : S, (Z s).TotalSpace` of the stratum total spaces with the reconstructed total space of the
glued core over the identity of `B` and the identity on every fibre `F`. Consequently, maps into or
out of the glued total space are continuous if and only if their restrictions to every clopen
stratum are continuous (`continuous_mk_ofLocallyConstant_iff`,
`continuous_from_ofLocallyConstant_iff`).
-/

public section

open Bundle Set Topology

namespace VectorBundleCore

variable {𝕜 B F S : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem mem_image_baseSet_iff (c : LocallyConstant B S)
    (Z : ∀ s : S, VectorBundleCore 𝕜 {b : B // c b = s} F {b : B // c b = s})
    {s : S} {i x : B} (hi : c i = s) (hx : c x = s) :
    x ∈ Subtype.val '' (Z (c i)).baseSet ⟨i, rfl⟩ ↔ ⟨x, hx⟩ ∈ (Z s).baseSet ⟨i, hi⟩ := by
  subst hi
  constructor
  · rintro ⟨⟨y, hy⟩, hmem, rfl⟩
    exact hmem
  · intro hmem
    exact ⟨⟨x, hx⟩, hmem, rfl⟩

private noncomputable def ofLocallyConstantCoordChange (c : LocallyConstant B S)
    (Z : ∀ s : S, VectorBundleCore 𝕜 {b : B // c b = s} F {b : B // c b = s})
    (i j x : B) : F →L[𝕜] F :=
  open Classical in
  if h : c i = c x ∧ c j = c x then
    (Z (c x)).coordChange ⟨i, h.1⟩ ⟨j, h.2⟩ ⟨x, rfl⟩
  else 0

private theorem ofLocallyConstantCoordChange_eq (c : LocallyConstant B S)
    (Z : ∀ s : S, VectorBundleCore 𝕜 {b : B // c b = s} F {b : B // c b = s})
    {s : S} {i j x : B} (hi : c i = s) (hj : c j = s) (hx : c x = s) :
    ofLocallyConstantCoordChange c Z i j x =
      (Z s).coordChange ⟨i, hi⟩ ⟨j, hj⟩ ⟨x, hx⟩ := by
  subst hx
  simp only [ofLocallyConstantCoordChange, hi, hj, and_self, ↓reduceDIte]

/-- Glue point-indexed vector-bundle cores on the clopen strata of `c : LocallyConstant B S` into a
single point-indexed `VectorBundleCore` over `B`. -/
noncomputable def ofLocallyConstant (c : LocallyConstant B S)
    (Z : ∀ s : S, VectorBundleCore 𝕜 {b : B // c b = s} F {b : B // c b = s})
    (hZ : ∀ s x, (Z s).indexAt x = x) :
    VectorBundleCore 𝕜 B F B where
  baseSet i := Subtype.val '' (Z (c i)).baseSet ⟨i, rfl⟩
  isOpen_baseSet i :=
    (c.isLocallyConstant.isOpen_fiber (c i)).isOpenEmbedding_subtypeVal.isOpenMap _
      ((Z (c i)).isOpen_baseSet ⟨i, rfl⟩)
  indexAt b := b
  mem_baseSet_at x :=
    ⟨⟨x, rfl⟩, by simpa only [hZ] using (Z (c x)).mem_baseSet_at ⟨x, rfl⟩, rfl⟩
  coordChange := ofLocallyConstantCoordChange c Z
  coordChange_self i x hx v := by
    rcases hx with ⟨⟨x, hxi⟩, hmem, rfl⟩
    rw [ofLocallyConstantCoordChange_eq c Z rfl rfl hxi]
    exact (Z (c i)).coordChange_self ⟨i, rfl⟩ ⟨x, hxi⟩ hmem v
  continuousOn_coordChange i j := by
    by_cases hij : c i = c j
    · let g : ↥((Subtype.val '' (Z (c i)).baseSet ⟨i, rfl⟩) ∩
          (Subtype.val '' (Z (c j)).baseSet ⟨j, rfl⟩)) → {b : B // c b = c i} :=
        fun x => ⟨x.1, by rcases x.2.1 with ⟨y, _, hy⟩; exact hy ▸ y.2⟩
      have hg : Continuous g := continuous_subtype_val.subtype_mk _
      have hmem : ∀ x, g x ∈ (Z (c i)).baseSet ⟨i, rfl⟩ ∩ (Z (c i)).baseSet ⟨j, hij.symm⟩ :=
        fun x => ⟨(mem_image_baseSet_iff c Z rfl (g x).2).mp x.2.1,
          (mem_image_baseSet_iff c Z hij.symm (g x).2).mp x.2.2⟩
      rw [continuousOn_iff_continuous_domRestrict]
      refine (((Z (c i)).continuousOn_coordChange ⟨i, rfl⟩ ⟨j, hij.symm⟩).comp_continuous
        hg hmem).congr fun x => ?_
      exact (ofLocallyConstantCoordChange_eq c Z rfl hij.symm (g x).2).symm
    · refine (continuousOn_empty _).mono fun x hx => False.elim (hij ?_)
      rcases hx.1 with ⟨y, _, rfl⟩
      rcases hx.2 with ⟨z, _, hz⟩
      exact y.2.symm.trans (hz ▸ z.2)
  coordChange_comp i j k x hx v := by
    rcases hx.1.1 with ⟨y₁, _, hy₁⟩
    rcases hx.1.2 with ⟨y₂, _, hy₂⟩
    rcases hx.2 with ⟨y₃, _, hy₃⟩
    have hi : c i = c x := (hy₁ ▸ y₁.2).symm
    have hj : c j = c x := (hy₂ ▸ y₂.2).symm
    have hk : c k = c x := (hy₃ ▸ y₃.2).symm
    rw [ofLocallyConstantCoordChange_eq c Z hj hk rfl,
      ofLocallyConstantCoordChange_eq c Z hi hj rfl,
      ofLocallyConstantCoordChange_eq c Z hi hk rfl]
    exact (Z (c x)).coordChange_comp ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ ⟨x, rfl⟩
      ⟨⟨(mem_image_baseSet_iff c Z hi rfl).mp hx.1.1,
        (mem_image_baseSet_iff c Z hj rfl).mp hx.1.2⟩,
        (mem_image_baseSet_iff c Z hk rfl).mp hx.2⟩ v

section API

variable (c : LocallyConstant B S)
  (Z : ∀ s : S, VectorBundleCore 𝕜 {b : B // c b = s} F {b : B // c b = s})
  (hZ : ∀ s x, (Z s).indexAt x = x)

@[simp] theorem indexAt_ofLocallyConstant (b : B) :
    (ofLocallyConstant c Z hZ).indexAt b = b := (rfl)

theorem baseSet_ofLocallyConstant (i : B) :
    (ofLocallyConstant c Z hZ).baseSet i = Subtype.val '' (Z (c i)).baseSet ⟨i, rfl⟩ := (rfl)

@[simp] theorem localTriv_baseSet_ofLocallyConstant (i : B) :
    ((ofLocallyConstant c Z hZ).localTriv i).baseSet =
      Subtype.val '' (Z (c i)).baseSet ⟨i, rfl⟩ := (rfl)

/-- Membership in a chart domain of `ofLocallyConstant` on stratum `s` reduces to membership in the
corresponding chart domain of `Z s`. -/
theorem mem_baseSet_ofLocallyConstant_iff {s : S} {i x : B} (hi : c i = s) (hx : c x = s) :
    x ∈ (ofLocallyConstant c Z hZ).baseSet i ↔ ⟨x, hx⟩ ∈ (Z s).baseSet ⟨i, hi⟩ :=
  mem_image_baseSet_iff c Z hi hx

/-- On a single clopen stratum `s`, the transition operator of `ofLocallyConstant` agrees with that
of `Z s`. -/
theorem coordChange_ofLocallyConstant_of_eq {s : S} {i j x : B}
    (hi : c i = s) (hj : c j = s) (hx : c x = s) :
    (ofLocallyConstant c Z hZ).coordChange i j x =
      (Z s).coordChange ⟨i, hi⟩ ⟨j, hj⟩ ⟨x, hx⟩ :=
  ofLocallyConstantCoordChange_eq c Z hi hj hx

/-- Every chart of `ofLocallyConstant` restricts on stratum `s` to the corresponding chart of
`Z s`. -/
theorem localTriv_ofLocallyConstant_apply {s : S} (i : {b : B // c b = s})
    (p : (Z s).TotalSpace) :
    (ofLocallyConstant c Z hZ).localTriv i.1 ⟨p.proj.1, p.2⟩ =
      (p.proj.1, ((Z s).localTriv i p).2) := by
  simp only [localTriv_apply, indexAt_ofLocallyConstant, hZ]
  exact Prod.ext rfl
    (DFunLike.congr_fun (coordChange_ofLocallyConstant_of_eq c Z hZ p.proj.2 i.2 p.proj.2) p.2)

private theorem continuous_stratum_to_ofLocallyConstant (s : S) :
    Continuous (fun p : (Z s).TotalSpace =>
      (⟨p.proj.1, p.2⟩ : (ofLocallyConstant c Z hZ).TotalSpace)) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(continuous_subtype_val.comp (Z s).continuous_proj).continuousAt, ?_⟩
  have hp := (Z s).mem_source_at p.proj p.2
  have hc := (((Z s).localTrivAt p.proj).continuousOn.continuousAt
    (((Z s).localTrivAt p.proj).open_source.mem_nhds hp)).snd
  refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  dsimp only [Function.comp_apply, VectorBundleCore.trivializationAt, localTrivAt]
  rw [indexAt_ofLocallyConstant, hZ]
  exact congrArg Prod.snd (localTriv_ofLocallyConstant_apply c Z hZ p.proj q)

private theorem continuous_ofLocallyConstant_to_stratum (s : S) :
    Continuous (fun q : {q : (ofLocallyConstant c Z hZ).TotalSpace // c q.proj = s} =>
      (⟨⟨q.1.proj, q.2⟩, q.1.2⟩ : (Z s).TotalSpace)) := by
  refine continuous_iff_continuousAt.2 fun q => ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(((ofLocallyConstant c Z hZ).continuous_proj.comp
    continuous_subtype_val).subtype_mk _).continuousAt, ?_⟩
  have hp := (ofLocallyConstant c Z hZ).mem_source_at q.1.proj q.1.2
  have htriv := ((ofLocallyConstant c Z hZ).localTrivAt q.1.proj).continuousOn.continuousAt
    (x := q.1) (((ofLocallyConstant c Z hZ).localTrivAt q.1.proj).open_source.mem_nhds hp)
  have hc := htriv.snd.comp (continuous_subtype_val.continuousAt (x := q))
  refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q' => ?_)
  dsimp only [Function.comp_apply, VectorBundleCore.trivializationAt, localTrivAt]
  rw [indexAt_ofLocallyConstant, hZ]
  exact (congrArg Prod.snd
    (localTriv_ofLocallyConstant_apply c Z hZ ⟨q.1.proj, q.2⟩ ⟨⟨q'.1.proj, q'.2⟩, q'.1.2⟩)).symm

/-- Reindexing the disjoint union of the stratum total spaces gives a homeomorphism onto the
reconstructed total space of `ofLocallyConstant`, covering the identity on `B` and acting as the
identity on every fibre `F`. -/
noncomputable def ofLocallyConstantHomeomorph :
    (Σ s : S, (Z s).TotalSpace) ≃ₜ (ofLocallyConstant c Z hZ).TotalSpace where
  toFun p := ⟨p.2.proj.1, p.2.2⟩
  invFun q := ⟨c q.proj, ⟨⟨q.proj, rfl⟩, q.2⟩⟩
  left_inv := by
    rintro ⟨s, ⟨⟨x, hx⟩, v⟩⟩
    cases hx
    rfl
  right_inv := by
    rintro ⟨x, v⟩
    rfl
  continuous_toFun := continuous_sigma (continuous_stratum_to_ofLocallyConstant c Z hZ)
  continuous_invFun := by
    apply continuous_of_cover_nhds
      (s := fun s : S => {q : (ofLocallyConstant c Z hZ).TotalSpace | c q.proj = s})
    · intro q
      exact ⟨c q.proj,
        ((c.isLocallyConstant.isOpen_fiber _).preimage
          (ofLocallyConstant c Z hZ).continuous_proj).mem_nhds rfl⟩
    · intro s
      rw [continuousOn_iff_continuous_domRestrict]
      refine (continuous_sigmaMk.comp
        (continuous_ofLocallyConstant_to_stratum c Z hZ s)).congr ?_
      rintro ⟨⟨x, v⟩, hx⟩
      cases hx
      rfl

@[simp] theorem ofLocallyConstantHomeomorph_apply (s : S) (p : (Z s).TotalSpace) :
    ofLocallyConstantHomeomorph c Z hZ ⟨s, p⟩ = ⟨p.proj.1, p.2⟩ := (rfl)

@[simp] theorem ofLocallyConstantHomeomorph_symm_apply
    (q : (ofLocallyConstant c Z hZ).TotalSpace) :
    (ofLocallyConstantHomeomorph c Z hZ).symm q = ⟨c q.proj, ⟨⟨q.proj, rfl⟩, q.2⟩⟩ := (rfl)

/-- Each stratum total space embeds openly into the glued total space. -/
theorem isOpenEmbedding_ofLocallyConstant_stratum (s : S) :
    IsOpenEmbedding (fun p : (Z s).TotalSpace =>
      (⟨p.proj.1, p.2⟩ : (ofLocallyConstant c Z hZ).TotalSpace)) :=
  (ofLocallyConstantHomeomorph c Z hZ).isOpenEmbedding.comp IsOpenEmbedding.sigmaMk

/-- The image of the `s`-stratum total space is the preimage of `{s}` under `c ∘ proj`. -/
theorem range_ofLocallyConstant_stratum (s : S) :
    Set.range (fun p : (Z s).TotalSpace =>
      (⟨p.proj.1, p.2⟩ : (ofLocallyConstant c Z hZ).TotalSpace)) =
      {q : (ofLocallyConstant c Z hZ).TotalSpace | c q.proj = s} := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact p.proj.2
  · intro hq
    exact ⟨⟨⟨q.proj, hq⟩, q.2⟩, rfl⟩

/-- A map into `(ofLocallyConstant c Z hZ).TotalSpace` over a continuous base map `b : Y → B` is
continuous if and only if its restriction to every clopen stratum `{y : Y // c (b y) = s}` is
continuous into `(Z s).TotalSpace`. -/
theorem continuous_mk_ofLocallyConstant_iff {Y : Type*} [TopologicalSpace Y] {b : Y → B}
    (hb : Continuous b) (v : Y → F) :
    Continuous (fun y => (⟨b y, v y⟩ : (ofLocallyConstant c Z hZ).TotalSpace)) ↔
      ∀ s : S, Continuous (fun y : {y : Y // c (b y) = s} =>
        (⟨⟨b y, y.2⟩, v y⟩ : (Z s).TotalSpace)) := by
  constructor
  · intro hv s
    apply (IsEmbedding.sigmaMk (σ := fun s => (Z s).TotalSpace)).continuous_iff.2
    refine ((ofLocallyConstantHomeomorph c Z hZ).symm.continuous.comp
      (hv.comp continuous_subtype_val)).congr ?_
    rintro ⟨y, hy⟩
    cases hy
    rfl
  · intro hv
    apply continuous_of_cover_nhds (s := fun s : S => {y : Y | c (b y) = s})
    · intro y
      exact ⟨c (b y), ((c.isLocallyConstant.isOpen_fiber _).preimage hb).mem_nhds rfl⟩
    · intro s
      rw [continuousOn_iff_continuous_domRestrict]
      exact (ofLocallyConstantHomeomorph c Z hZ).continuous.comp (continuous_sigmaMk.comp (hv s))

/-- A map out of `(ofLocallyConstant c Z hZ).TotalSpace` is continuous if and only if its
composition with every stratum inclusion is continuous. -/
theorem continuous_from_ofLocallyConstant_iff {Y : Type*} [TopologicalSpace Y]
    {g : (ofLocallyConstant c Z hZ).TotalSpace → Y} :
    Continuous g ↔ ∀ s : S, Continuous (fun p : (Z s).TotalSpace => g ⟨p.proj.1, p.2⟩) :=
  (ofLocallyConstantHomeomorph c Z hZ).comp_continuous_iff'.symm.trans continuous_sigma_iff

end API

end VectorBundleCore
