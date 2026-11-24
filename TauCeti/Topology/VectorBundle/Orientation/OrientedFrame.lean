/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal
public import TauCeti.Topology.VectorBundle.Orientation.OrthonormalFrame
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Reduction

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
acts on the positively oriented frames on the right, continuously, freely and transitively on each
fibre, by the action shared by such reductions (`TauCeti.OrthonormalFrameBundle.SMulMemIff`), and
every fibre contains a positively oriented frame when the rank is positive
(`TauCeti.OrthonormalFrameBundle.exists_mem_orientedFrames`).

In positive rank the positively oriented frames are locally trivial with fibre the special
orthogonal group, by trivializations equivariant for the action
(`TauCeti.OrthonormalFrameBundle.exists_trivialization_orientedFrames`). Over the base set of an
equivariant trivialization of the orthonormal frame bundle, its local frame `σ` is positively
oriented on a clopen subset of the base set; on the complement, composing `σ` with an orthogonal
transformation `r` of determinant `-1` makes it positively oriented. Dividing by the corrected
frame trivializes the positively oriented frames, by the construction shared by all such
reductions (`TauCeti.OrthonormalFrameBundle.exists_trivialization_of_continuousOn_smul_mem`). This
is the reduction of the structure group of the orthonormal frame bundle from the orthogonal group
to the special orthogonal group given by the orientation.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.orientedFrames s o`: the orthonormal frames transporting the
  orientation `o` of `V` to the orientation `s` of the bundle.
* The instance `TauCeti.OrthonormalFrameBundle.SMulMemIff (TauCeti.specialOrthogonalGroup V)
  (orientedFrames s o)`, giving the right action of the special orthogonal group on the positively
  oriented frames.

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

namespace TauCeti.OrthonormalFrameBundle

section Oriented

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*}
  (s : VectorBundleOrientation F E ι) (o : Orientation ℝ V ι)

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

variable [Fintype ι]

/-- The frames that are not positively oriented for `o` are those positively oriented for the
opposite orientation `-o`, provided `card ι` is the dimension of `V`. -/
theorem compl_orientedFrames (hι : Fintype.card ι = finrank ℝ V) :
    (orientedFrames s o)ᶜ = (orientedFrames s (-o) : Set (OrthonormalFrameBundle ℝ F E V)) := by
  ext p
  have hp : Fintype.card ι = finrank ℝ (E p.proj) := hι.trans p.frame.toLinearEquiv.finrank_eq
  simp only [mem_compl_iff, mem_orientedFrames_iff, Orientation.map_neg]
  rcases Orientation.eq_or_eq_neg_of_card_eq_finrank (s p.proj)
      (Orientation.map ι p.frame.toLinearEquiv o) hp with h | h <;> rw [h]
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

/-- Every fibre contains a positively oriented frame, provided the rank `card ι` is positive and
equal to the dimension of `V` and of the model fibre. -/
theorem exists_mem_orientedFrames [Nonempty ι] (hι : Fintype.card ι = finrank ℝ V)
    (hF : Fintype.card ι = finrank ℝ F) (x : B) :
    ∃ p ∈ (orientedFrames s o : Set (OrthonormalFrameBundle ℝ F E V)), p.proj = x := by
  obtain ⟨p, hp⟩ := surjective_toOrientationCover (F := F) (E := E) (V := V) hι hF o ⟨x, s x⟩
  rw [toOrientationCover_eq_mk] at hp
  obtain rfl : p.proj = x := congrArg VectorBundleOrientationCover.proj hp
  exact ⟨p, VectorBundleOrientationCover.mk_eq_mk_iff.1 hp, rfl⟩

section Action

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
  · rw [key, (o.map_eq_iff_det_pos_of_card_eq_finrank _ hι).2
      (mem_specialOrthogonalGroup_iff_det_pos.1 hg)]
    exact iff_of_true hp hg
  · rw [key, (o.map_eq_neg_iff_det_neg _ hι).2 (notMem_specialOrthogonalGroup_iff_det_neg.1 hg),
      ← notMem_orientedFrames_iff hι]
    exact iff_of_false (not_not.2 hp) hg

/-- The orthogonal transformations carrying a positively oriented frame to a positively oriented
frame are the special orthogonal ones, which therefore act on the positively oriented frames on the
right, freely and transitively on fibres. -/
instance [Fact (Fintype.card ι = finrank ℝ V)] :
    SMulMemIff (specialOrthogonalGroup V) (orientedFrames s o) :=
  ⟨smul_mem_orientedFrames_iff Fact.out⟩

end Action

end Oriented

/-! ### Local triviality -/

section OrientedTrivialization

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*}
  (s : VectorBundleOrientation F E ι) (o : Orientation ℝ V ι)
  [Fintype ι] [CompleteSpace V] [Fact (Fintype.card ι = finrank ℝ V)]

section Trivialization

variable
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

variable {s o T r}

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

end Trivialization

/-- In positive rank the positively oriented frames are locally trivial with fibre the special
orthogonal group, by trivializations equivariant for its right action: this is the principal
`SO(n)`-bundle of an oriented Riemannian vector bundle of rank `n = card ι ≥ 1`. -/
theorem exists_trivialization_orientedFrames [ContinuousFiberNorm F E] [Nonempty ι]
    (hF : Fintype.card ι = finrank ℝ F) (x : B) :
    ∃ t : Trivialization (specialOrthogonalGroup V)
        (fun p : orientedFrames s o ↦ (p : OrthonormalFrameBundle ℝ F E V).proj),
      x ∈ t.baseSet ∧ ∀ (g : specialOrthogonalGroup V) (p : orientedFrames s o),
        (p : OrthonormalFrameBundle ℝ F E V).proj ∈ t.baseSet →
          t (op g • p) = ((t p).1, (t p).2 * g) := by
  have hι : Fintype.card ι = finrank ℝ V := Fact.out
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (hι ▸ Fintype.card_pos)
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (hF ▸ Fintype.card_pos)
  obtain ⟨T, hx, hT⟩ := exists_trivialization (E := E) (V := V) (hι.symm.trans hF) x
  obtain ⟨r, hr⟩ := Unitary.exists_det_eq_neg_one (V := V) (hι ▸ Fintype.card_pos)
  have hr' : r ∉ specialOrthogonalGroup V :=
    notMem_specialOrthogonalGroup_iff_det_neg.2 (by rw [hr]; norm_num)
  have : T.orthonormalFrameBundleFiber.IsEquivariant :=
    T.isEquivariant_orthonormalFrameBundleFiber_iff.2 fun p _ g ↦ congrArg Prod.snd (hT g p)
  -- The local frame of `T`, corrected by `correction`, is positively oriented over `T.baseSet`.
  obtain ⟨t, ht, hteq⟩ := exists_trivialization_of_continuousOn_smul_mem
    (H := specialOrthogonalGroup V) subset_rfl
    (fun y _ ↦ smul_localFrame_mem (s := s) (o := o) hr' y) T.open_baseSet
    (fun _ hy ↦ (continuousAt_correction (s := s) (o := o) (r := r) (·⁻¹) hy).continuousWithinAt)
    hx
  exact ⟨t, ht ▸ hx, fun g p hp ↦ hteq g p (ht ▸ hp)⟩

end OrientedTrivialization

end TauCeti.OrthonormalFrameBundle
