/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orientation
public import TauCeti.Topology.VectorBundle.Orientation.Cover
public import TauCeti.Topology.VectorBundle.OrthonormalFrame

/-!
# The orientation double cover as a quotient of the orthonormal frame bundle

Let `E → B` be a continuous Riemannian vector bundle with model fibre `F` of rank `n ≥ 1`, and let
`V` be an `n`-dimensional real inner product space with an orientation `o`. An orthonormal frame
`V ≃ₗᵢ[ℝ] E b` transports `o` to an orientation of the fibre `E b`, which defines a map
`TauCeti.OrthonormalFrameBundle.toOrientationCover o` from the orthonormal frame bundle to the
orientation double cover of `E`.

Acting on a frame by an orthogonal transformation `g` of `V` keeps its orientation when
`det g > 0` and reverses it when `det g < 0`, so two frames have the same orientation exactly when
they differ by an element of the special orthogonal group of `V`
(`TauCeti.OrthonormalFrameBundle.toOrientationCover_eq_toOrientationCover_iff`). The map is
continuous, because the frames read in a trivialization form a continuous family of linear maps,
whose determinant sign is locally constant; it is open, because a local orthonormal frame through
a given frame is a continuous local section; and it is surjective, because every orientation of a
fibre is the image of a positively oriented orthonormal basis. So the orientation double cover is
homeomorphic to the quotient of the orthonormal frame bundle by the right action of the special
orthogonal group (`TauCeti.OrthonormalFrameBundle.orientationCoverHomeomorph`). Reversing `o`
composes this homeomorphism with the deck involution
(`TauCeti.OrthonormalFrameBundle.toOrientationCover_neg`).

In rank `0` there is a single frame over each point while the fibre has two orientations, so the
nonemptiness of the index type `ι` is needed for surjectivity.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.toOrientationCover`: the orientation of the fibre determined by
  an orthonormal frame and an orientation of the model space.
* `TauCeti.OrthonormalFrameBundle.orientedRel`: the relation of differing by a special orthogonal
  transformation.
* `TauCeti.OrthonormalFrameBundle.orientationCoverHomeomorph`: the homeomorphism from the quotient
  of the orthonormal frame bundle by `orientedRel` onto the orientation double cover.

## Main results

* `TauCeti.OrthonormalFrameBundle.toOrientationCover_eq_toOrientationCover_iff`: two frames have
  the same orientation exactly when they differ by a special orthogonal transformation.
* `TauCeti.OrthonormalFrameBundle.continuous_toOrientationCover`,
  `TauCeti.OrthonormalFrameBundle.isOpenMap_toOrientationCover`,
  `TauCeti.OrthonormalFrameBundle.surjective_toOrientationCover`: the map to the orientation double
  cover is continuous, open and surjective.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §§9, 12 (orientations, the orientation double cover, and the oriented
  structure group `SO(n)`).
* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 6, §2 (reduction of the structure group of the orthonormal frame bundle to
  `SO(n)` by an orientation).
-/

public section

noncomputable section

open Bundle Filter Module Set MulOpposite
open scoped Topology

variable {B : Type*} {F : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*}

namespace TauCeti.OrthonormalFrameBundle

/-- The orientation of the fibre determined by an orthonormal frame: the frame transports the
orientation `o` of the model space `V` to the fibre over its base point. -/
def toOrientationCover (o : Orientation ℝ V ι) (p : OrthonormalFrameBundle F E V) :
    VectorBundleOrientationCover F E ι :=
  ⟨p.proj, Orientation.map ι p.frame.toLinearEquiv o⟩

@[simp]
theorem proj_toOrientationCover (o : Orientation ℝ V ι) (p : OrthonormalFrameBundle F E V) :
    (toOrientationCover o p).proj = p.proj :=
  (rfl)

/-- The frame transports the orientation of the model space to the fibre over its base point. -/
@[simp]
theorem orientation_toOrientationCover (o : Orientation ℝ V ι)
    (p : OrthonormalFrameBundle F E V) :
    (proj_toOrientationCover o p) ▸ (toOrientationCover o p).orientation =
      Orientation.map ι p.frame.toLinearEquiv o :=
  (rfl)

section Action

variable [CompleteSpace V]

/-- Acting on a frame by an orthogonal transformation `g` amounts to transporting the orientation
of the model space along `g` first. -/
theorem toOrientationCover_smul (o : Orientation ℝ V ι) (g : unitary (V →L[ℝ] V))
    (p : OrthonormalFrameBundle F E V) :
    toOrientationCover o (op g • p) =
      toOrientationCover (Orientation.map ι (Unitary.linearIsometryEquiv g).toLinearEquiv o) p :=
  VectorBundleOrientationCover.mk_eq_mk_iff.2 (Orientation.map_trans _ _ o)

variable [Fintype ι] [FiniteDimensional ℝ V]

/-- An orthogonal transformation of positive determinant preserves the orientation of a frame. -/
theorem toOrientationCover_smul_of_det_pos (hι : Fintype.card ι = finrank ℝ V)
    (o : Orientation ℝ V ι) {g : unitary (V →L[ℝ] V)} (hg : 0 < (g : V →L[ℝ] V).det)
    (p : OrthonormalFrameBundle F E V) :
    toOrientationCover o (op g • p) = toOrientationCover o p := by
  rw [toOrientationCover_smul, (o.map_eq_iff_det_pos _ hι).2 hg]

/-- Two orthonormal frames determine the same orientation exactly when they differ by an
orthogonal transformation of positive determinant. -/
theorem toOrientationCover_eq_toOrientationCover_iff (hι : Fintype.card ι = finrank ℝ V)
    (o : Orientation ℝ V ι) {p q : OrthonormalFrameBundle F E V} :
    toOrientationCover o p = toOrientationCover o q ↔
      ∃ g : unitary (V →L[ℝ] V), 0 < (g : V →L[ℝ] V).det ∧ q = op g • p := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg, hq⟩ ↦ hq ▸ (toOrientationCover_smul_of_det_pos hι o hg p).symm⟩
  obtain ⟨g, rfl⟩ := exists_smul_eq_iff.2 (congrArg VectorBundleOrientationCover.proj h)
  refine ⟨g, ?_, rfl⟩
  rw [toOrientationCover_smul] at h
  -- Both orientations live on the fibre over `p.proj`, where transport along the frame of `p`
  -- is injective.
  have h' := (Orientation.map ι p.frame.toLinearEquiv).injective
    (VectorBundleOrientationCover.mk_eq_mk_iff.1 h)
  exact (o.map_eq_iff_det_pos _ hι).1 h'.symm

variable (F E V) in
/-- The relation on orthonormal frames of differing by a special orthogonal transformation of `V`,
that is, an orthogonal transformation of positive determinant. Its quotient is the orientation
double cover (`TauCeti.OrthonormalFrameBundle.orientationCoverHomeomorph`). -/
def orientedRel : Setoid (OrthonormalFrameBundle F E V) where
  r p q := ∃ g : unitary (V →L[ℝ] V), 0 < (g : V →L[ℝ] V).det ∧ q = op g • p
  -- By `toOrientationCover_eq_toOrientationCover_iff`, for any orientation of `V`, the relation
  -- says that the two frames give the same orientation of the fibre.
  iseqv := by
    have h (p q : OrthonormalFrameBundle F E V) :=
      toOrientationCover_eq_toOrientationCover_iff (p := p) (q := q)
        (Fintype.card_fin (finrank ℝ V)) (Module.finBasis ℝ V).orientation
    exact ⟨fun p ↦ (h p p).1 rfl, fun {p q} hpq ↦ (h q p).1 ((h p q).2 hpq).symm,
      fun {p q r} hpq hqr ↦ (h p r).1 (((h p q).2 hpq).trans ((h q r).2 hqr))⟩

/-- Unfolds `orientedRel`: two frames are related when they differ by an orthogonal
transformation of positive determinant. -/
theorem orientedRel_iff {p q : OrthonormalFrameBundle F E V} :
    orientedRel F E V p q ↔ ∃ g : unitary (V →L[ℝ] V), 0 < (g : V →L[ℝ] V).det ∧ q = op g • p :=
  Iff.rfl

/-- The relation `orientedRel` is the kernel of the map to the orientation double cover, for any
orientation of `V`. -/
theorem orientedRel_eq_ker (hι : Fintype.card ι = finrank ℝ V) (o : Orientation ℝ V ι) :
    orientedRel F E V = Setoid.ker (toOrientationCover o) :=
  Setoid.ext fun _ _ ↦ (toOrientationCover_eq_toOrientationCover_iff hι o).symm

end Action

variable [TopologicalSpace (TotalSpace F E)] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace B] [FiberBundle F E] [VectorBundle ℝ F E]

/-- Reversing the orientation of the model space reverses the orientation of every fibre. -/
theorem toOrientationCover_neg (o : Orientation ℝ V ι) (p : OrthonormalFrameBundle F E V) :
    toOrientationCover (-o) p = VectorBundleOrientationCover.deck (toOrientationCover o p) := by
  rw [VectorBundleOrientationCover.deck_apply]
  exact VectorBundleOrientationCover.mk_eq_mk_iff.2 (Module.Ray.map_neg _ o)

variable [Fintype ι] [FiniteDimensional ℝ V]

/-- An orthogonal transformation of negative determinant reverses the orientation of a frame. -/
theorem toOrientationCover_smul_of_det_neg (hι : Fintype.card ι = finrank ℝ V)
    (o : Orientation ℝ V ι) {g : unitary (V →L[ℝ] V)} (hg : (g : V →L[ℝ] V).det < 0)
    (p : OrthonormalFrameBundle F E V) :
    toOrientationCover o (op g • p) =
      VectorBundleOrientationCover.deck (toOrientationCover o p) := by
  rw [toOrientationCover_smul, (o.map_eq_neg_iff_det_neg _ hι).2 hg, toOrientationCover_neg]

omit [VectorBundle ℝ F E] in
/-- Read in a linear trivialization `e`, the orientation transported by the frames is locally
constant. -/
private theorem eventually_mapOrientation_eq (hι : Fintype.card ι = finrank ℝ V)
    (o : Orientation ℝ V ι) (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {p₀ : OrthonormalFrameBundle F E V} (h₀ : p₀.proj ∈ e.baseSet) :
    ∀ᶠ q in 𝓝 p₀, ∃ hq : q.proj ∈ e.baseSet,
      e.mapOrientation ι hq (Orientation.map ι q.frame.toLinearEquiv o) =
        e.mapOrientation ι h₀ (Orientation.map ι p₀.frame.toLinearEquiv o) := by
  -- The frames near `p₀`, read in `e` and then read back in the frame `p₀`, form a continuous
  -- family of endomorphisms of `V` equal to the identity at `p₀`, so their determinants stay
  -- positive near `p₀`.
  have hU : proj ⁻¹' e.baseSet ∈ 𝓝 p₀ := (e.open_baseSet.preimage continuous_proj).mem_nhds h₀
  -- `L q` is the frame at `q` read in `e`.
  let L (q : OrthonormalFrameBundle F E V) (hq : q.proj ∈ e.baseSet) : V ≃L[ℝ] F :=
    q.frame.toContinuousLinearEquiv.trans (e.continuousLinearEquivAt ℝ q.proj hq)
  have hL {q : OrthonormalFrameBundle F E V} (hq : q.proj ∈ e.baseSet) :
      (L q hq).toLinearEquiv = q.frame.toLinearEquiv.trans (e.linearEquivAt ℝ q.proj hq) :=
    rfl
  have hcoord {q : OrthonormalFrameBundle F E V} (hq : q.proj ∈ e.baseSet) :
      (((L p₀ h₀).symm : F →L[ℝ] V).comp (coord e q) : V →ₗ[ℝ] V) =
        ((L q hq).trans (L p₀ h₀).symm).toLinearEquiv := by
    ext v
    simp [L, coord_apply hq, e.continuousLinearEquivAt_apply (R := ℝ)]
  let d : OrthonormalFrameBundle F E V → ℝ := fun q ↦
    (((L p₀ h₀).symm : F →L[ℝ] V).comp (coord e q)).det
  have hd : ContinuousAt d p₀ := ContinuousLinearMap.continuous_det.continuousAt.comp
    (continuousAt_const.clm_comp ((continuousOn_coord e).continuousAt hU))
  have hd₀ : d p₀ = 1 := by
    simp only [d, ContinuousLinearMap.det, hcoord h₀, ContinuousLinearEquiv.self_trans_symm]
    exact LinearMap.det_id
  filter_upwards [hU, hd.eventually (lt_mem_nhds (hd₀ ▸ one_pos))] with q hq hdq
  refine ⟨hq, ?_⟩
  have hpos : Orientation.map ι ((L q hq).trans (L p₀ h₀).symm).toLinearEquiv o = o := by
    refine (o.map_eq_iff_det_pos _ hι).2 ?_
    rwa [← hcoord hq]
  simp only [Trivialization.mapOrientation_apply, ← Orientation.map_trans, ← hL]
  calc Orientation.map ι (L q hq).toLinearEquiv o
      = Orientation.map ι (L p₀ h₀).toLinearEquiv
          (Orientation.map ι ((L q hq).trans (L p₀ h₀).symm).toLinearEquiv o) := by
        rw [← Orientation.map_trans]
        refine congrArg (fun f : V ≃ₗ[ℝ] F ↦ Orientation.map ι f o) (LinearEquiv.ext fun v ↦ ?_)
        simp
    _ = Orientation.map ι (L p₀ h₀).toLinearEquiv o := by rw [hpos]

/-- The map from the orthonormal frame bundle to the orientation double cover is continuous. -/
theorem continuous_toOrientationCover (hι : Fintype.card ι = finrank ℝ V)
    (o : Orientation ℝ V ι) :
    Continuous (toOrientationCover o : OrthonormalFrameBundle F E V → _) :=
  VectorBundleOrientationCover.continuous_of_isOpen_preimage_sheet continuous_proj
    fun b oF ↦ isOpen_iff_mem_nhds.2 fun p₀ hp₀ ↦ by
      obtain ⟨h₀, hp₀⟩ := VectorBundleOrientationCover.mem_sheet_iff.1 hp₀
      filter_upwards [eventually_mapOrientation_eq hι o _ h₀] with q ⟨hq, hq'⟩
      exact VectorBundleOrientationCover.mem_sheet_iff.2 ⟨hq, hq'.trans hp₀⟩

omit [FiniteDimensional ℝ V] in
/-- Over a point of the base, every orientation of the fibre is transported from `o` by some
orthonormal frame, provided the rank `card ι` is positive and equal to the dimension of `V` and of
the model fibre. -/
theorem surjective_toOrientationCover [Nonempty ι] (hι : Fintype.card ι = finrank ℝ V)
    (hF : Fintype.card ι = finrank ℝ F) (o : Orientation ℝ V ι) :
    Function.Surjective (toOrientationCover o : OrthonormalFrameBundle F E V → _) := by
  rintro ⟨b, o'⟩
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
  obtain ⟨φ, hφ⟩ := Orientation.exists_linearIsometryEquiv_map_eq hι.symm
    (((trivializationAt F E b).linearEquivAt ℝ b hb).finrank_eq.trans hF.symm) o o'
  exact ⟨⟨b, φ⟩, VectorBundleOrientationCover.mk_eq_mk_iff.2 hφ⟩

variable [IsContinuousRiemannianBundle F E]

/-- The map from the orthonormal frame bundle to the orientation double cover is open, provided
`card ι` is the dimension of `V` and of the model fibre. -/
theorem isOpenMap_toOrientationCover [FiniteDimensional ℝ F] (hι : Fintype.card ι = finrank ℝ V)
    (hF : Fintype.card ι = finrank ℝ F) (o : Orientation ℝ V ι) :
    IsOpenMap (toOrientationCover o : OrthonormalFrameBundle F E V → _) := by
  refine IsOpenMap.of_nhds_le fun p₀ ↦ ?_
  obtain ⟨T, hT, -⟩ := exists_trivialization (E := E) (hι.symm.trans hF) p₀.proj
  -- The local section `s` of the frame bundle over `T.baseSet` through `p₀`.
  let s (y : B) : OrthonormalFrameBundle F E V := T.toOpenPartialHomeomorph.symm (y, (T p₀).2)
  have hs : ContinuousOn s T.baseSet := T.toOpenPartialHomeomorph.continuousOn_symm.comp
    (continuousOn_id.prodMk continuousOn_const) fun y hy ↦ T.mem_target.2 hy
  have hsproj {y : B} (hy : y ∈ T.baseSet) : (s y).proj = y := T.proj_symm_apply' hy
  have hs₀ : s p₀.proj = p₀ := T.symm_apply_mk_proj (T.mem_source.2 hT)
  -- Near `toOrientationCover o p₀`, a point `q` of the double cover is the orientation transported
  -- by the frame `s q.proj`: both are continuous sections of the covering projection over
  -- `T.baseSet` through this point.
  have hN : {q | toOrientationCover o (s q.proj) = q} ∈ 𝓝 (toOrientationCover o p₀) := by
    let U : Set (VectorBundleOrientationCover F E ι) := VectorBundleOrientationCover.proj ⁻¹'
      T.baseSet
    have hU : IsOpen U := VectorBundleOrientationCover.isOpen_preimage_proj T.open_baseSet
    have hcont : Continuous fun q : U ↦ toOrientationCover o (s q.1.proj) :=
      (continuous_toOrientationCover hι o).comp (hs.comp_continuous
        (VectorBundleOrientationCover.continuous_proj.comp continuous_subtype_val) fun q ↦ q.2)
    have hopen := (VectorBundleOrientationCover.isCoveringMap_proj hF).isLocalHomeomorph
      |>.isLocallyInjective.isOpen_eqLocus hcont continuous_subtype_val
        (funext fun q ↦ hsproj q.2)
    refine Filter.mem_of_superset ((hU.isOpenMap_subtype_val _ hopen).mem_nhds
      ⟨⟨toOrientationCover o p₀, hT⟩, by simp [hs₀], rfl⟩) ?_
    rintro _ ⟨q, hq, rfl⟩
    exact hq
  have hsc : Tendsto (fun q : VectorBundleOrientationCover F E ι ↦ s q.proj)
      (𝓝 (toOrientationCover o p₀)) (𝓝 p₀) := by
    have h := ((hs.continuousAt (T.open_baseSet.mem_nhds hT)).comp_of_eq
      VectorBundleOrientationCover.continuous_proj.continuousAt
      (proj_toOrientationCover o p₀)).tendsto
    simpa only [Function.comp_def, proj_toOrientationCover, hs₀] using h
  calc 𝓝 (toOrientationCover o p₀)
      = map (fun q ↦ toOrientationCover o (s q.proj)) (𝓝 (toOrientationCover o p₀)) := by
        rw [map_congr (eventually_of_mem hN fun q hq ↦ hq), map_id']
    _ ≤ map (toOrientationCover o) (𝓝 p₀) := tendsto_map.comp hsc

/-- When `card ι` is positive and equal to the dimension of `V` and of the model fibre, the map
from the orthonormal frame bundle to the orientation double cover is an open quotient map. -/
theorem isOpenQuotientMap_toOrientationCover [Nonempty ι] [FiniteDimensional ℝ F]
    (hι : Fintype.card ι = finrank ℝ V) (hF : Fintype.card ι = finrank ℝ F)
    (o : Orientation ℝ V ι) :
    IsOpenQuotientMap (toOrientationCover o : OrthonormalFrameBundle F E V → _) where
  surjective := surjective_toOrientationCover hι hF o
  continuous := continuous_toOrientationCover hι o
  isOpenMap := isOpenMap_toOrientationCover hι hF o

/-- The orientation double cover of `E` is the quotient of the orthonormal frame bundle by the
right action of the special orthogonal group of `V`: when `card ι` is positive and equal to the
dimension of `V` and of the model fibre, transporting the orientation `o` of `V` along frames
descends to a homeomorphism from the quotient by `orientedRel` onto the orientation double cover.
It sends the class of a frame `p` to `toOrientationCover o p`
(`TauCeti.OrthonormalFrameBundle.orientationCoverHomeomorph_mk`). -/
def orientationCoverHomeomorph [Nonempty ι] [FiniteDimensional ℝ F]
    (hι : Fintype.card ι = finrank ℝ V) (hF : Fintype.card ι = finrank ℝ F)
    (o : Orientation ℝ V ι) :
    Quotient (orientedRel F E V) ≃ₜ VectorBundleOrientationCover F E ι :=
  (Homeomorph.Quotient.congrRight (Setoid.ext_iff.1 (orientedRel_eq_ker hι o))).trans
    (Topology.IsQuotientMap.homeomorph (f := ⟨_, continuous_toOrientationCover hι o⟩)
      (isOpenQuotientMap_toOrientationCover hι hF o).isQuotientMap)

/-- The homeomorphism `orientationCoverHomeomorph` sends the class of a frame to the orientation
it transports. -/
@[simp]
theorem orientationCoverHomeomorph_mk [Nonempty ι] [FiniteDimensional ℝ F]
    (hι : Fintype.card ι = finrank ℝ V) (hF : Fintype.card ι = finrank ℝ F)
    (o : Orientation ℝ V ι) (p : OrthonormalFrameBundle F E V) :
    orientationCoverHomeomorph hι hF o (Quotient.mk _ p) = toOrientationCover o p :=
  (rfl)

end TauCeti.OrthonormalFrameBundle
