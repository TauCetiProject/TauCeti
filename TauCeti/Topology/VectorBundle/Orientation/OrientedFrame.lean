/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal
public import TauCeti.Topology.VectorBundle.Orientation.OrthonormalFrame

/-!
# The oriented orthonormal frame bundle

Let `E → B` be a continuous Riemannian vector bundle with model fibre `F`, oriented by
`s : TauCeti.VectorBundleOrientation F E ι`, and let `V` be a real inner product space with an
orientation `o`, where `card ι` is the dimension of `V`. An orthonormal frame `V ≃ₗᵢ[ℝ] E b` is
*positively oriented* when it transports `o` to the orientation `s b` of the fibre. The positively
oriented frames form the subset `TauCeti.OrthonormalFrameBundle.orientedFrames s o` of the
orthonormal frame bundle; equivalently, they are the frames whose image in the orientation double
cover lies on the section given by `s`
(`TauCeti.OrthonormalFrameBundle.mem_orientedFrames_iff_toOrientationCover`).

This subset is clopen (`TauCeti.OrthonormalFrameBundle.isClopen_orientedFrames`): it is open since
the orientation transported by a frame varies continuously, and its complement is the set of
frames that are positively oriented for the opposite orientation `-o`
(`TauCeti.OrthonormalFrameBundle.compl_orientedFrames`). Acting by an orthogonal transformation
`g` of `V` keeps a positively oriented frame positively oriented exactly when `g` lies in the
special orthogonal group `TauCeti.specialOrthogonalGroup V`
(`TauCeti.OrthonormalFrameBundle.smul_mem_orientedFrames_iff`). So the special orthogonal group
acts on the positively oriented frames on the right, continuously, freely
(`TauCeti.OrthonormalFrameBundle.orientedFrames_smul_eq_self_iff`) and transitively on each fibre
(`TauCeti.OrthonormalFrameBundle.exists_orientedFrames_smul_eq_iff`), and every fibre contains a
positively oriented frame when the rank is positive
(`TauCeti.OrthonormalFrameBundle.exists_mem_orientedFrames`).

In positive rank the positively oriented frames are locally trivial with fibre the special
orthogonal group, by trivializations equivariant for the action
(`TauCeti.OrthonormalFrameBundle.exists_trivialization_orientedFrames`). Over the base set of an
equivariant trivialization of the orthonormal frame bundle, its local frame `σ` is positively
oriented on a clopen subset of the base set; on the complement, composing `σ` with an orthogonal
transformation `r` of determinant `-1` makes it positively oriented. Dividing by the corrected
frame trivializes the positively oriented frames. This is the reduction of the structure group of
the orthonormal frame bundle from the orthogonal group to the special orthogonal group given by
the orientation.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.orientedFrames s o`: the orthonormal frames transporting the
  orientation `o` of `V` to the orientation `s` of the bundle.
* The right action of `TauCeti.specialOrthogonalGroup V` on `orientedFrames s o`.

## Main results

* `TauCeti.OrthonormalFrameBundle.isClopen_orientedFrames`: the positively oriented frames form a
  clopen set.
* `TauCeti.OrthonormalFrameBundle.smul_mem_orientedFrames_iff`: an orthogonal transformation keeps
  a positively oriented frame positively oriented exactly when it is special orthogonal.
* `TauCeti.OrthonormalFrameBundle.exists_trivialization_orientedFrames`: the positively oriented
  frames are locally trivial with fibre the special orthogonal group, equivariantly for the
  action.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (oriented bundles and the structure group `SO(n)`).
* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 6, §2 (reduction of the structure group of the orthonormal frame bundle to
  `SO(n)` by an orientation).
-/

public section

noncomputable section

open Bundle Filter Module Set MulOpposite
open scoped Topology

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*}

namespace TauCeti.OrthonormalFrameBundle

variable (s : VectorBundleOrientation F E ι) (o : Orientation ℝ V ι)

/-- The positively oriented orthonormal frames of an oriented Riemannian vector bundle: the frames
`V ≃ₗᵢ[ℝ] E b` that transport the orientation `o` of `V` to the orientation `s b` of the
fibre. -/
def orientedFrames : Set (OrthonormalFrameBundle ℝ F E V) :=
  {p | Orientation.map ι p.frame.toLinearEquiv o = s p.proj}

variable {s o}

/-- A frame is positively oriented when it transports `o` to the orientation of the fibre. -/
@[simp]
theorem mem_orientedFrames_iff {p : OrthonormalFrameBundle ℝ F E V} :
    p ∈ orientedFrames s o ↔ Orientation.map ι p.frame.toLinearEquiv o = s p.proj :=
  Iff.rfl

/-- A frame is positively oriented exactly when its image in the orientation double cover lies on
the section given by the orientation `s`. -/
theorem mem_orientedFrames_iff_toOrientationCover {p : OrthonormalFrameBundle ℝ F E V} :
    p ∈ orientedFrames s o ↔ toOrientationCover o p = ⟨p.proj, s p.proj⟩ := by
  rw [toOrientationCover_eq_mk, VectorBundleOrientationCover.mk_eq_mk_iff, mem_orientedFrames_iff]

variable [Fintype ι] [FiniteDimensional ℝ V]

/-- The frames that are not positively oriented for `o` are those positively oriented for the
opposite orientation `-o`, provided `card ι` is the dimension of `V`. -/
theorem compl_orientedFrames (hι : Fintype.card ι = finrank ℝ V) :
    (orientedFrames s o)ᶜ = (orientedFrames s (-o) : Set (OrthonormalFrameBundle ℝ F E V)) := by
  ext p
  have := p.frame.toLinearEquiv.finiteDimensional
  have hp : Fintype.card ι = finrank ℝ (E p.proj) := hι.trans p.frame.toLinearEquiv.finrank_eq
  simp only [mem_compl_iff, mem_orientedFrames_iff, Orientation.map_neg]
  rcases Orientation.eq_or_eq_neg (s p.proj) (Orientation.map ι p.frame.toLinearEquiv o) hp
    with h | h <;> rw [h]
  · exact iff_of_false (not_not.2 rfl) (Module.Ray.ne_neg_self _).symm
  · exact iff_of_true (Module.Ray.ne_neg_self _) rfl

/-- A frame is not positively oriented for `o` exactly when it is positively oriented for the
opposite orientation `-o`, provided `card ι` is the dimension of `V`. -/
theorem notMem_orientedFrames_iff (hι : Fintype.card ι = finrank ℝ V)
    {p : OrthonormalFrameBundle ℝ F E V} : p ∉ orientedFrames s o ↔ p ∈ orientedFrames s (-o) := by
  rw [← mem_compl_iff, compl_orientedFrames hι]

/-! ### Topology -/

/-- The positively oriented frames form an open set, provided `card ι` is the dimension of
`V`. -/
theorem isOpen_orientedFrames (hι : Fintype.card ι = finrank ℝ V) :
    IsOpen (orientedFrames s o : Set (OrthonormalFrameBundle ℝ F E V)) := by
  convert s.isOpen_setOf_orientation_eq.preimage (continuous_toOrientationCover hι o) using 1
  ext p
  simp only [mem_preimage, mem_ofPred_eq, toOrientationCover_eq_mk, mem_orientedFrames_iff]

/-- The positively oriented frames form a clopen set, provided `card ι` is the dimension of
`V`. -/
theorem isClopen_orientedFrames (hι : Fintype.card ι = finrank ℝ V) :
    IsClopen (orientedFrames s o : Set (OrthonormalFrameBundle ℝ F E V)) :=
  ⟨by rw [← isOpen_compl_iff, compl_orientedFrames hι]; exact isOpen_orientedFrames hι,
    isOpen_orientedFrames hι⟩

omit [FiniteDimensional ℝ V] in
/-- Every fibre contains a positively oriented frame, provided the rank `card ι` is positive and
equal to the dimension of `V` and of the model fibre. -/
theorem exists_mem_orientedFrames [Nonempty ι] (hι : Fintype.card ι = finrank ℝ V)
    (hF : Fintype.card ι = finrank ℝ F) (x : B) :
    ∃ p ∈ (orientedFrames s o : Set (OrthonormalFrameBundle ℝ F E V)), p.proj = x := by
  obtain ⟨p, hp⟩ := surjective_toOrientationCover (F := F) (E := E) (V := V) hι hF o ⟨x, s x⟩
  rw [toOrientationCover_eq_mk] at hp
  obtain rfl : p.proj = x := congrArg VectorBundleOrientationCover.proj hp
  exact ⟨p, VectorBundleOrientationCover.mk_eq_mk_iff.1 hp, rfl⟩

variable [CompleteSpace V]

/-- An orthogonal transformation `g` of `V` keeps a positively oriented frame positively oriented
exactly when `g` is special orthogonal, provided `card ι` is the dimension of `V`. -/
theorem smul_mem_orientedFrames_iff (hι : Fintype.card ι = finrank ℝ V)
    {p : OrthonormalFrameBundle ℝ F E V} (hp : p ∈ orientedFrames s o) {g : unitary (V →L[ℝ] V)} :
    op g • p ∈ orientedFrames s o ↔ g ∈ specialOrthogonalGroup V := by
  have key : op g • p ∈ orientedFrames s o ↔ p ∈ orientedFrames s
      (Orientation.map ι (Unitary.linearIsometryEquiv g).toLinearEquiv o) := by
    rw [mem_orientedFrames_iff_toOrientationCover, mem_orientedFrames_iff_toOrientationCover,
      toOrientationCover_smul, proj_smul]
  by_cases hg : g ∈ specialOrthogonalGroup V
  · rw [key, (o.map_eq_iff_det_pos _ hι).2 (mem_specialOrthogonalGroup_iff_det_pos.1 hg)]
    exact iff_of_true hp hg
  · rw [key, (o.map_eq_neg_iff_det_neg _ hι).2 (notMem_specialOrthogonalGroup_iff_det_neg.1 hg),
      ← notMem_orientedFrames_iff hι]
    exact iff_of_false (not_not.2 hp) hg

/-- Two positively oriented frames over the same base point differ by a special orthogonal
transformation. -/
theorem exists_mem_specialOrthogonalGroup_smul_eq (hι : Fintype.card ι = finrank ℝ V)
    {p q : OrthonormalFrameBundle ℝ F E V} (hp : p ∈ orientedFrames s o)
    (hq : q ∈ orientedFrames s o) (h : p.proj = q.proj) :
    ∃ g ∈ specialOrthogonalGroup V, op g • p = q := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_iff.2 h
  exact ⟨g, (smul_mem_orientedFrames_iff hι hp).1 hq, rfl⟩

/-! ### The right action of the special orthogonal group -/

section Action

variable [Fact (Fintype.card ι = finrank ℝ V)]

/-- The right action of the special orthogonal group of `V` on the positively oriented frames, by
precomposition. -/
instance : MulAction (specialOrthogonalGroup V)ᵐᵒᵖ (orientedFrames s o) where
  smul g p := ⟨op (g.unop : unitary (V →L[ℝ] V)) • p.1,
    (smul_mem_orientedFrames_iff Fact.out p.2).2 g.unop.2⟩
  one_smul p := Subtype.ext (one_smul _ p.1)
  mul_smul g h p := Subtype.ext (mul_smul (op (g.unop : unitary (V →L[ℝ] V)))
    (op (h.unop : unitary (V →L[ℝ] V))) p.1)

/-- The action on positively oriented frames is the action on all orthonormal frames. -/
@[simp]
theorem coe_orientedFrames_smul (g : (specialOrthogonalGroup V)ᵐᵒᵖ) (p : orientedFrames s o) :
    ((g • p : orientedFrames s o) : OrthonormalFrameBundle ℝ F E V) =
      op (g.unop : unitary (V →L[ℝ] V)) • (p : OrthonormalFrameBundle ℝ F E V) :=
  rfl

/-- The action of the special orthogonal group on positively oriented frames is free. -/
@[simp]
theorem orientedFrames_smul_eq_self_iff {g : specialOrthogonalGroup V} {p : orientedFrames s o} :
    op g • p = p ↔ g = 1 := by
  rw [← Subtype.coe_inj, coe_orientedFrames_smul, unop_op, smul_eq_self_iff,
    OneMemClass.coe_eq_one]

/-- The action of the special orthogonal group on positively oriented frames is transitive on
fibres: two positively oriented frames differ by a special orthogonal transformation exactly when
they lie over the same base point. -/
theorem exists_orientedFrames_smul_eq_iff {p q : orientedFrames s o} :
    (∃ g : specialOrthogonalGroup V, op g • p = q) ↔ p.1.proj = q.1.proj := by
  refine ⟨fun ⟨g, h⟩ ↦ by rw [← h, coe_orientedFrames_smul, proj_smul], fun h ↦ ?_⟩
  obtain ⟨g, hg, hgq⟩ := exists_mem_specialOrthogonalGroup_smul_eq Fact.out p.2 q.2 h
  exact ⟨⟨g, hg⟩, Subtype.ext hgq⟩

end Action

variable [Fact (Fintype.card ι = finrank ℝ V)]

/-- The right action of the special orthogonal group on positively oriented frames is
continuous. -/
instance : ContinuousSMul (specialOrthogonalGroup V)ᵐᵒᵖ (orientedFrames s o) where
  continuous_smul := ((continuous_op.comp ((continuous_subtype_val.comp continuous_unop).comp
    continuous_fst)).smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-! ### Local triviality -/

section Trivialization

variable (s o)
  (T : Trivialization (unitary (V →L[ℝ] V)) (proj : OrthonormalFrameBundle ℝ F E V → B))
  (r : unitary (V →L[ℝ] V))

/-- The local frame of the trivialization `T` at `y`: the frame with fibre coordinate `1`. -/
private abbrev localFrame (y : B) : OrthonormalFrameBundle ℝ F E V :=
  T.toOpenPartialHomeomorph.symm (y, 1)

open scoped Classical in
/-- The correction of the local frame of `T` at `y`: `1` where it is positively oriented, and
`r⁻¹` elsewhere. Composing the local frame with its inverse makes it positively oriented. -/
private def correction (y : B) : unitary (V →L[ℝ] V) :=
  if localFrame T y ∈ orientedFrames s o then 1 else r⁻¹

open scoped Classical in
/-- An orthogonal transformation, as an element of the special orthogonal group when it is one,
and `1` otherwise. -/
private def toSpecialOrthogonal (g : unitary (V →L[ℝ] V)) : specialOrthogonalGroup V :=
  if h : g ∈ specialOrthogonalGroup V then ⟨g, h⟩ else 1

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E] [Fintype ι]
  [FiniteDimensional ℝ V] [Fact (Fintype.card ι = finrank ℝ V)] in
/-- The trivialization `T` of the orthonormal frame bundle is equivariant: it turns the right action
of the orthogonal group into right multiplication on the fibre coordinate, as for the
trivializations of `TauCeti.OrthonormalFrameBundle.exists_trivialization`. -/
private abbrev IsEquivariant : Prop :=
  ∀ (g : unitary (V →L[ℝ] V)) (p : OrthonormalFrameBundle ℝ F E V),
    T (op g • p) = ((T p).1, (T p).2 * g)

variable {s o T r}

omit [FiniteDimensional ℝ V] [Fact (Fintype.card ι = finrank ℝ V)] in
private theorem coe_toSpecialOrthogonal {g : unitary (V →L[ℝ] V)}
    (hg : g ∈ specialOrthogonalGroup V) : (toSpecialOrthogonal g : unitary (V →L[ℝ] V)) = g := by
  simp [toSpecialOrthogonal, hg]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E] [Fintype ι]
  [FiniteDimensional ℝ V] [Fact (Fintype.card ι = finrank ℝ V)] in
/-- Over the base set of an equivariant trivialization, every frame is the local frame acted on
by its fibre coordinate. -/
private theorem eq_smul_localFrame
    (hT : IsEquivariant T)
    {p : OrthonormalFrameBundle ℝ F E V} (hp : p.proj ∈ T.baseSet) :
    p = op (T p).2 • localFrame T p.proj := by
  have hσp : (localFrame T p.proj).proj = p.proj := T.proj_symm_apply' hp
  refine T.injOn (T.mem_source.2 hp) (T.mem_source.2 (hσp.symm ▸ hp : _)) ?_
  rw [T.coe_coe, hT, T.apply_symm_apply' hp, one_mul]
  exact Prod.ext (T.coe_fst' hp) rfl

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E] [Fintype ι]
  [FiniteDimensional ℝ V] [Fact (Fintype.card ι = finrank ℝ V)] in
/-- The inverse of an equivariant trivialization at `(y, g)` is the local frame at `y` acted on
by `g`. -/
private theorem symm_apply_eq_smul
    (hT : IsEquivariant T)
    {y : B} (hy : y ∈ T.baseSet) (g : unitary (V →L[ℝ] V)) :
    T.toOpenPartialHomeomorph.symm (y, g) = op g • localFrame T y := by
  have hproj : (T.toOpenPartialHomeomorph.symm (y, g)).proj = y := T.proj_symm_apply' hy
  have hy' : (T.toOpenPartialHomeomorph.symm (y, g)).proj ∈ T.baseSet := by rwa [hproj]
  exact (eq_smul_localFrame hT hy').trans (by rw [hproj, T.apply_symm_apply' hy])

/-- The local frame of `T` composed with its correction is positively oriented. -/
private theorem smul_localFrame_mem (hr : r ∉ specialOrthogonalGroup V) (y : B) :
    op (correction s o T r y)⁻¹ • localFrame T y ∈ orientedFrames s o := by
  unfold correction
  split_ifs with h
  · simpa using h
  · rw [inv_inv]
    by_contra hn
    exact (smul_mem_orientedFrames_iff Fact.out ((notMem_orientedFrames_iff Fact.out).1 h)).not.2 hr
      ((notMem_orientedFrames_iff Fact.out).1 hn)

/-- Over the base set of `T`, a frame is positively oriented exactly when its fibre coordinate,
multiplied by the correction, is special orthogonal. -/
private theorem mem_orientedFrames_iff_correction_mul_mem
    (hT : IsEquivariant T)
    (hr : r ∉ specialOrthogonalGroup V) {p : OrthonormalFrameBundle ℝ F E V}
    (hp : p.proj ∈ T.baseSet) :
    p ∈ orientedFrames s o ↔
      correction s o T r p.proj * (T p).2 ∈ specialOrthogonalGroup V := by
  have h : p = op (correction s o T r p.proj * (T p).2) •
      (op (correction s o T r p.proj)⁻¹ • localFrame T p.proj) := by
    rw [smul_smul, ← op_mul, inv_mul_cancel_left]
    exact eq_smul_localFrame hT hp
  conv_lhs => rw [h]
  exact smul_mem_orientedFrames_iff Fact.out (smul_localFrame_mem hr p.proj)

/-- Over the base set of `T`, the inverse of `T` at a point with corrected special orthogonal
fibre coordinate is positively oriented. -/
private theorem symm_mem_orientedFrames
    (hT : IsEquivariant T)
    (hr : r ∉ specialOrthogonalGroup V) {y : B} (hy : y ∈ T.baseSet)
    {g : unitary (V →L[ℝ] V)} (hg : g ∈ specialOrthogonalGroup V) :
    T.toOpenPartialHomeomorph.symm (y, (correction s o T r y)⁻¹ * g) ∈ orientedFrames s o := by
  rw [symm_apply_eq_smul hT hy, op_mul, mul_smul]
  exact (smul_mem_orientedFrames_iff Fact.out (smul_localFrame_mem hr y)).2 hg

/-- The correction is locally constant over the base set of `T`. -/
private theorem eventually_correction_eq {y : B} (hy : y ∈ T.baseSet) :
    ∀ᶠ z in 𝓝 y, correction s o T r z = correction s o T r y := by
  have hσ : ContinuousAt (localFrame T) y :=
    (T.toOpenPartialHomeomorph.continuousOn_symm.continuousAt
      (T.open_target.mem_nhds (T.mem_target.2 hy))).comp
      (continuousAt_id.prodMk continuousAt_const)
  by_cases h : localFrame T y ∈ orientedFrames s o
  · filter_upwards [hσ.preimage_mem_nhds ((isOpen_orientedFrames Fact.out).mem_nhds h)] with z hz
    simp [correction, mem_preimage.1 hz, h]
  · have h' := (notMem_orientedFrames_iff Fact.out).1 h
    filter_upwards [hσ.preimage_mem_nhds ((isOpen_orientedFrames Fact.out).mem_nhds h')] with z hz
    simp [correction, (notMem_orientedFrames_iff Fact.out).2 hz, h]

/-- A function of the correction is continuous at the points of the base set of `T`. -/
private theorem continuousAt_correction {X : Type*} [TopologicalSpace X]
    (f : unitary (V →L[ℝ] V) → X) {y : B} (hy : y ∈ T.baseSet) :
    ContinuousAt (fun z ↦ f (correction s o T r z)) y :=
  continuousAt_const.congr
    ((eventually_correction_eq (s := s) (o := o) (r := r) hy).mono fun _ hz ↦ congrArg f hz.symm)

open scoped Classical in
variable (s o r) in
/-- The trivialization of the positively oriented frames over the base set of an equivariant
trivialization `T` of the orthonormal frame bundle, with fibre the special orthogonal group: a
frame `p` over `y` goes to `(y, c y * (T p).2)`, where `c` is the correction making the local frame
of `T` positively oriented. The positively oriented frame `p₀` is a junk value of the inverse off
its target. -/
private def orientedTrivialization
    (hT : IsEquivariant T)
    (hr : r ∉ specialOrthogonalGroup V) (p₀ : orientedFrames s o) :
    Trivialization (specialOrthogonalGroup V)
      (fun p : orientedFrames s o ↦ (p : OrthonormalFrameBundle ℝ F E V).proj) where
  toFun p := (p.1.proj, toSpecialOrthogonal (correction s o T r p.1.proj * (T p.1).2))
  invFun q :=
    if h : T.toOpenPartialHomeomorph.symm (q.1, (correction s o T r q.1)⁻¹ * q.2) ∈
        orientedFrames s o then ⟨_, h⟩ else p₀
  source := {p | p.1.proj ∈ T.baseSet}
  target := T.baseSet ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' q hq := by
    rw [mem_ofPred_eq, dite_eq_left (symm_mem_orientedFrames hT hr hq.1 q.2.2),
      T.proj_symm_apply' hq.1]
    exact hq.1
  left_inv' p hp := by
    have hm := (mem_orientedFrames_iff_correction_mul_mem hT hr hp).1 p.2
    have hTp : T.toOpenPartialHomeomorph.symm (p.1.proj, (correction s o T r p.1.proj)⁻¹ *
        (toSpecialOrthogonal (correction s o T r p.1.proj * (T p.1).2) :
          unitary (V →L[ℝ] V))) = p.1 := by
      rw [coe_toSpecialOrthogonal hm, inv_mul_cancel_left]
      conv_lhs => rw [← T.coe_fst' hp]
      exact T.toOpenPartialHomeomorph.left_inv (T.mem_source.2 hp)
    dsimp only
    split_ifs with h
    · exact Subtype.ext hTp
    · exact absurd (by rw [hTp]; exact p.2) h
  right_inv' q hq := by
    rw [dite_eq_left (symm_mem_orientedFrames hT hr hq.1 q.2.2)]
    rw [T.proj_symm_apply' hq.1, T.apply_symm_apply' hq.1, mul_inv_cancel_left]
    exact Prod.ext rfl (Subtype.ext (coe_toSpecialOrthogonal q.2.2))
  open_source := T.open_baseSet.preimage (continuous_proj.comp continuous_subtype_val)
  open_target := T.open_baseSet.prod isOpen_univ
  continuousOn_toFun := by
    refine (continuous_proj.comp continuous_subtype_val).continuousOn.prodMk ?_
    refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 (ContinuousOn.congr
      (f := fun p : orientedFrames s o ↦ correction s o T r p.1.proj * (T p.1).2) ?_
      fun p hp ↦ coe_toSpecialOrthogonal
        ((mem_orientedFrames_iff_correction_mul_mem hT hr hp).1 p.2))
    refine ContinuousOn.mul (fun p hp ↦ ?_) (continuous_snd.comp_continuousOn
      (T.continuousOn_toFun.comp continuous_subtype_val.continuousOn fun p hp ↦
        T.mem_source.2 hp))
    exact ((continuousAt_correction id hp).comp (f := fun p : orientedFrames s o ↦ p.1.proj)
      (continuous_proj.comp continuous_subtype_val).continuousAt).continuousWithinAt
  continuousOn_invFun := by
    refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 (ContinuousOn.congr
      (f := fun q : B × specialOrthogonalGroup V ↦
        T.toOpenPartialHomeomorph.symm (q.1, (correction s o T r q.1)⁻¹ * q.2)) ?_
      fun q hq ↦ by
        simp only [Function.comp_apply, dite_eq_left (symm_mem_orientedFrames hT hr hq.1 q.2.2)])
    refine T.toOpenPartialHomeomorph.continuousOn_symm.comp (continuousOn_fst.prodMk ?_)
      fun q hq ↦ T.mem_target.2 hq.1
    refine ContinuousOn.mul (fun q hq ↦ ?_)
      (continuous_subtype_val.comp continuous_snd).continuousOn
    exact ((continuousAt_correction (·⁻¹) hq.1).comp
      continuous_fst.continuousAt).continuousWithinAt
  baseSet := T.baseSet
  open_baseSet := T.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

private theorem orientedTrivialization_apply
    (hT : IsEquivariant T)
    (hr : r ∉ specialOrthogonalGroup V) (p₀ : orientedFrames s o) (p : orientedFrames s o) :
    orientedTrivialization s o r hT hr p₀ p =
      (p.1.proj, toSpecialOrthogonal (correction s o T r p.1.proj * (T p.1).2)) :=
  rfl

/-- The trivialization `orientedTrivialization` is equivariant over its base set. -/
private theorem orientedTrivialization_smul
    (hT : IsEquivariant T)
    (hr : r ∉ specialOrthogonalGroup V) (p₀ : orientedFrames s o) (g : specialOrthogonalGroup V)
    {p : orientedFrames s o} (hp : (p : OrthonormalFrameBundle ℝ F E V).proj ∈ T.baseSet) :
    orientedTrivialization s o r hT hr p₀ (op g • p) =
      ((orientedTrivialization s o r hT hr p₀ p).1,
        (orientedTrivialization s o r hT hr p₀ p).2 * g) := by
  have h₁ := (mem_orientedFrames_iff_correction_mul_mem hT hr hp).1 p.2
  have h₂ := (mem_orientedFrames_iff_correction_mul_mem
    (p := ((op g • p : orientedFrames s o) : OrthonormalFrameBundle ℝ F E V)) hT hr hp).1
    (op g • p).2
  rw [coe_orientedFrames_smul, unop_op] at h₂
  simp only [orientedTrivialization_apply, coe_orientedFrames_smul, unop_op, proj_smul]
  refine Prod.ext rfl (Subtype.ext ?_)
  rw [Subgroup.coe_mul, coe_toSpecialOrthogonal h₁]
  rw [proj_smul] at h₂
  rw [coe_toSpecialOrthogonal h₂, hT, mul_assoc]

end Trivialization

variable (s o) in
/-- In positive rank the positively oriented frames are locally trivial with fibre the special
orthogonal group, by trivializations equivariant for its right action: this is the principal
`SO(n)`-bundle of an oriented Riemannian vector bundle of rank `n = card ι ≥ 1`. -/
theorem exists_trivialization_orientedFrames [IsContinuousRiemannianBundle F E]
    [FiniteDimensional ℝ F] [Nonempty ι] (hF : Fintype.card ι = finrank ℝ F) (x : B) :
    ∃ t : Trivialization (specialOrthogonalGroup V)
        (fun p : orientedFrames s o ↦ (p : OrthonormalFrameBundle ℝ F E V).proj),
      x ∈ t.baseSet ∧ ∀ (g : specialOrthogonalGroup V) (p : orientedFrames s o),
        (p : OrthonormalFrameBundle ℝ F E V).proj ∈ t.baseSet →
          t (op g • p) = ((t p).1, (t p).2 * g) := by
  have hι : Fintype.card ι = finrank ℝ V := Fact.out
  obtain ⟨T, hx, hT⟩ := exists_trivialization (E := E) (V := V) (hι.symm.trans hF) x
  obtain ⟨r, hr⟩ := Unitary.exists_det_eq_neg_one (V := V) (hι ▸ Fintype.card_pos)
  have hr' : r ∉ specialOrthogonalGroup V :=
    notMem_specialOrthogonalGroup_iff_det_neg.2 (by rw [hr]; norm_num)
  obtain ⟨p₀, hp₀, -⟩ := exists_mem_orientedFrames (s := s) (o := o) hι hF x
  exact ⟨orientedTrivialization s o r hT hr' ⟨p₀, hp₀⟩, hx,
    fun g p hp ↦ orientedTrivialization_smul hT hr' _ g hp⟩

end TauCeti.OrthonormalFrameBundle
