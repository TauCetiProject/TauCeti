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
`σ : TauCeti.VectorBundleOrientation F E ι`, and let `V` be a real inner product space with an
orientation `o`, where `card ι` is the dimension of `V` and of `F`. An orthonormal frame
`V ≃ₗᵢ[ℝ] E b` is positively oriented when it carries `o` to the orientation `σ b` of the fibre.
The positively oriented frames form the subset `TauCeti.OrthonormalFrameBundle.orientedFrames o σ`
of the orthonormal frame bundle. It is a principal bundle for the special orthogonal group
`TauCeti.specialOrthogonalGroup V`, the reduction of the structure group of the frame bundle from
the orthogonal group of `V` to its special orthogonal group determined by the orientation:

* an orthogonal transformation `g` carries a positively oriented frame to a positively oriented
  frame exactly when `g` is special orthogonal
  (`TauCeti.OrthonormalFrameBundle.smul_mem_orientedFrames_iff`);
* the special orthogonal group acts transitively on the positively oriented frames over each
  point (`TauCeti.OrthonormalFrameBundle.exists_mem_specialOrthogonalGroup_smul_eq_iff`), and
  freely, since the orthogonal group already does;
* the positively oriented frames form a clopen subset, whose complement consists of the frames
  positively oriented for `-σ` (`TauCeti.OrthonormalFrameBundle.isClopen_orientedFrames`,
  `TauCeti.OrthonormalFrameBundle.compl_orientedFrames`);
* when `card ι` is positive, every fibre contains a positively oriented frame
  (`TauCeti.OrthonormalFrameBundle.exists_mem_orientedFrames_proj_eq`);
* the positively oriented frames are locally trivial with fibre the special orthogonal group, by
  trivializations equivariant for the right action
  (`TauCeti.OrthonormalFrameBundle.exists_trivialization_orientedFrames`).

The local trivializations restrict equivariant trivializations of the orthonormal frame bundle
(`Bundle.Trivialization.restrictOrientedFrames`): if `t` is one, and `p₀` is a positively
oriented frame over its base set, then over the points `y` where the frame `t⁻¹ (y, g₀)` with
`g₀ = (t p₀).2` is positively oriented, the positively oriented frames are those of the form
`t⁻¹ (y, g₀ * g)` with `g` special orthogonal.

In rank `0` there is a single frame over each point, while the fibre has two orientations; so the
fibres of `orientedFrames o σ` are empty over the points where `σ` is opposite to the orientation
transported by that frame. This is why nonemptiness of the fibres asks `ι` to be nonempty.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.orientedFrames`: the positively oriented orthonormal frames.
* `Bundle.Trivialization.restrictOrientedFrames`: the restriction of an equivariant
  trivialization of the frame bundle to the positively oriented frames, with fibre the special
  orthogonal group.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (oriented bundles and the structure group `SO(n)`).
* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 6, §2 (reduction of the structure group of the orthonormal frame bundle to
  `SO(n)` by an orientation).
-/

public section

noncomputable section

open Bundle Module Set MulOpposite TauCeti

variable {B : Type*} {F : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*}
  [TopologicalSpace (TotalSpace F E)] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace B] [FiberBundle F E] [VectorBundle ℝ F E]

namespace TauCeti.OrthonormalFrameBundle

/-- The positively oriented orthonormal frames: the frames `V ≃ₗᵢ[ℝ] E b` carrying the
orientation `o` of `V` to the orientation `σ b` of the fibre. -/
def orientedFrames (o : Orientation ℝ V ι) (σ : VectorBundleOrientation F E ι) :
    Set (OrthonormalFrameBundle F E V) :=
  {p | Orientation.map ι p.frame.toLinearEquiv o = σ p.proj}

variable {o : Orientation ℝ V ι} {σ : VectorBundleOrientation F E ι}
  {p q : OrthonormalFrameBundle F E V}

@[simp]
theorem mem_orientedFrames_iff :
    p ∈ orientedFrames o σ ↔ Orientation.map ι p.frame.toLinearEquiv o = σ p.proj :=
  Iff.rfl

/-- A frame is positively oriented exactly when the orientation it transports is the point of
the orientation double cover given by `σ`. -/
theorem mem_orientedFrames_iff_toOrientationCover_eq :
    p ∈ orientedFrames o σ ↔ toOrientationCover o p = ⟨p.proj, σ p.proj⟩ := by
  rw [toOrientationCover_def, VectorBundleOrientationCover.mk_eq_mk_iff, mem_orientedFrames_iff]

/-- The frames positively oriented for `-o` are those positively oriented for `-σ`. -/
@[simp]
theorem orientedFrames_neg_left :
    orientedFrames (-o) σ = orientedFrames o (-σ) := by
  ext p
  rw [mem_orientedFrames_iff, mem_orientedFrames_iff, Orientation.map_neg,
    VectorBundleOrientation.neg_apply]
  -- The negation of `Orientation` reached through `InvolutiveNeg` is only reducibly the one in
  -- the goal, so `neg_neg` is applied to explicit arguments rather than rewritten with.
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]
    exact (_root_.neg_neg (Orientation.map ι p.frame.toLinearEquiv o)).symm
  · rw [h]
    exact _root_.neg_neg (σ p.proj)

section FiniteDimensional

variable [Fintype ι] [FiniteDimensional ℝ V]

/-- A frame is positively oriented for `σ` or for `-σ`, and not for both: the frames positively
oriented for `-σ` form the complement of those positively oriented for `σ`. -/
theorem compl_orientedFrames (hι : Fintype.card ι = finrank ℝ V) :
    (orientedFrames o σ)ᶜ = orientedFrames o (-σ) := by
  ext p
  have : FiniteDimensional ℝ (E p.proj) := p.frame.toLinearEquiv.finiteDimensional
  simp only [mem_compl_iff, mem_orientedFrames_iff, VectorBundleOrientation.neg_apply]
  rcases (Orientation.map ι p.frame.toLinearEquiv o).eq_or_eq_neg (σ p.proj)
    (hι.trans p.frame.toLinearEquiv.finrank_eq) with h | h
  · exact iff_of_false (· h) fun h' ↦ Module.Ray.ne_neg_self _ (h.symm.trans h')
  · exact iff_of_true (fun h' ↦ Module.Ray.ne_neg_self _ (h'.symm.trans h)) h

/-- The positively oriented frames form an open set: they are the inverse image, under the map
to the orientation double cover, of the open image of the section given by `σ`. -/
theorem isOpen_orientedFrames (hι : Fintype.card ι = finrank ℝ V) :
    IsOpen (orientedFrames o σ) := by
  have h : orientedFrames o σ = toOrientationCover o ⁻¹'
      {q : VectorBundleOrientationCover F E ι | q.orientation = σ q.proj} := by
    ext p
    rw [mem_preimage, toOrientationCover_def]
    -- Both sides now compare the orientation transported by `p` with `σ p.proj`.
    exact Iff.rfl
  rw [h]
  exact σ.isOpen_setOf_orientation_eq.preimage (continuous_toOrientationCover hι o)

/-- The positively oriented frames form a clopen subset of the orthonormal frame bundle. -/
theorem isClopen_orientedFrames (hι : Fintype.card ι = finrank ℝ V) :
    IsClopen (orientedFrames o σ) :=
  ⟨isOpen_compl_iff.1 (by rw [compl_orientedFrames hι]; exact isOpen_orientedFrames hι),
    isOpen_orientedFrames hι⟩

/-- An orthogonal transformation `g` carries a positively oriented frame to a positively oriented
frame exactly when `g` is special orthogonal. -/
theorem smul_mem_orientedFrames_iff (hι : Fintype.card ι = finrank ℝ V)
    {g : unitary (V →L[ℝ] V)} (hp : p ∈ orientedFrames o σ) :
    op g • p ∈ orientedFrames o σ ↔ g ∈ specialOrthogonalGroup V := by
  rw [mem_orientedFrames_iff_toOrientationCover_eq] at hp ⊢
  rw [toOrientationCover_smul, proj_smul,
    ← o.map_linearIsometryEquiv_eq_iff_mem_specialOrthogonalGroup hι]
  rcases (Orientation.map ι (Unitary.linearIsometryEquiv g).toLinearEquiv o).eq_or_eq_neg o hι
    with h | h
  · rw [h, hp]
    exact iff_of_true rfl rfl
  · rw [h, toOrientationCover_neg, hp]
    exact iff_of_false (VectorBundleOrientationCover.deck_ne_self _)
      fun h' ↦ Module.Ray.ne_neg_self o h'.symm

/-- The special orthogonal group acts transitively on the positively oriented frames over each
point: two positively oriented frames differ by a special orthogonal transformation exactly when
they lie over the same point. The transformation is unique, since the action of the orthogonal
group is free (`TauCeti.OrthonormalFrameBundle.smul_eq_self_iff`). -/
theorem exists_mem_specialOrthogonalGroup_smul_eq_iff (hι : Fintype.card ι = finrank ℝ V)
    (hp : p ∈ orientedFrames o σ) (hq : q ∈ orientedFrames o σ) :
    (∃ g ∈ specialOrthogonalGroup V, op g • p = q) ↔ p.proj = q.proj := by
  refine ⟨fun ⟨g, _, hg⟩ ↦ exists_smul_eq_iff.1 ⟨g, hg⟩, fun h ↦ ?_⟩
  obtain ⟨g, rfl⟩ := exists_smul_eq_iff.2 h
  exact ⟨g, (smul_mem_orientedFrames_iff hι hp).1 hq, rfl⟩

omit [FiniteDimensional ℝ V] in
/-- When `card ι` is positive and equal to the dimension of `V` and of the model fibre, every
fibre contains a positively oriented frame. -/
theorem exists_mem_orientedFrames_proj_eq [Nonempty ι] (hι : Fintype.card ι = finrank ℝ V)
    (hF : Fintype.card ι = finrank ℝ F) (o : Orientation ℝ V ι)
    (σ : VectorBundleOrientation F E ι) (b : B) :
    ∃ p ∈ orientedFrames o σ, p.proj = b := by
  obtain ⟨p, hp⟩ := surjective_toOrientationCover (F := F) (E := E) hι hF o ⟨b, σ b⟩
  obtain rfl : p.proj = b :=
    (proj_toOrientationCover o p).symm.trans (congrArg VectorBundleOrientationCover.proj hp)
  exact ⟨p, mem_orientedFrames_iff_toOrientationCover_eq.2 hp, rfl⟩

end FiniteDimensional

end TauCeti.OrthonormalFrameBundle

namespace Bundle.Trivialization

open OrthonormalFrameBundle

variable [Fintype ι] [FiniteDimensional ℝ V] (hι : Fintype.card ι = finrank ℝ V)
  {o : Orientation ℝ V ι} {σ : VectorBundleOrientation F E ι}
  (t : Trivialization (unitary (V →L[ℝ] V)) (proj : OrthonormalFrameBundle F E V → B))
  (ht : ∀ (g : unitary (V →L[ℝ] V)) (p : OrthonormalFrameBundle F E V),
    t (op g • p) = ((t p).1, (t p).2 * g))
  {p₀ : OrthonormalFrameBundle F E V} (hp₀ : p₀ ∈ orientedFrames o σ)

/-- The base set of `t.restrictOrientedFrames`: the points `y` of the base set of `t` where the
frame `t⁻¹ (y, g₀)`, with `g₀ = (t p₀).2`, is positively oriented. -/
private def orientedBaseSet (σ : VectorBundleOrientation F E ι) (o : Orientation ℝ V ι)
    (p₀ : OrthonormalFrameBundle F E V) : Set B :=
  t.baseSet ∩ (fun y ↦ t.toOpenPartialHomeomorph.symm (y, (t p₀).2)) ⁻¹' orientedFrames o σ

include hι in
private theorem isOpen_orientedBaseSet : IsOpen (t.orientedBaseSet σ o p₀) :=
  (t.toOpenPartialHomeomorph.continuousOn_symm.comp (continuousOn_id.prodMk continuousOn_const)
    fun _ hy ↦ t.mem_target.2 hy).isOpen_inter_preimage t.open_baseSet (isOpen_orientedFrames hι)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E] [VectorBundle ℝ F E] in
include ht in
/-- Over the base set of an equivariant trivialization, moving along the orthogonal group in the
fibre coordinate is the right action. -/
private theorem symm_mul_eq_smul {y : B} (hy : y ∈ t.baseSet) (g h : unitary (V →L[ℝ] V)) :
    t.toOpenPartialHomeomorph.symm (y, g * h) = op h • t.toOpenPartialHomeomorph.symm (y, g) := by
  refine t.injOn (t.map_target (t.mem_target.2 hy)) ?_ ?_
  · rw [t.mem_source, proj_smul, t.proj_symm_apply' hy]
    exact hy
  · rw [Trivialization.coe_coe, ht, t.apply_symm_apply' hy, t.apply_symm_apply' hy]

include hι ht in
/-- Over the base set of `t.restrictOrientedFrames`, the fibre coordinate of a positively oriented
frame differs from `(t p₀).2` by a special orthogonal transformation. -/
private theorem inv_mul_mem_specialOrthogonalGroup {p : OrthonormalFrameBundle F E V}
    (hp : p ∈ orientedFrames o σ) (hy : p.proj ∈ t.orientedBaseSet σ o p₀) :
    (t p₀).2⁻¹ * (t p).2 ∈ specialOrthogonalGroup V := by
  obtain ⟨g, hg, hgp⟩ := (exists_mem_specialOrthogonalGroup_smul_eq_iff hι hy.2 hp).2
    (t.proj_symm_apply' hy.1)
  rw [← hgp, ht, t.apply_symm_apply' hy.1, inv_mul_cancel_left]
  exact hg

include hι ht in
/-- Over the base set of `t.restrictOrientedFrames`, the frames whose fibre coordinate differs from
`(t p₀).2` by a special orthogonal transformation are positively oriented. -/
private theorem symm_mul_mem_orientedFrames {y : B} (hy : y ∈ t.orientedBaseSet σ o p₀)
    {g : unitary (V →L[ℝ] V)} (hg : g ∈ specialOrthogonalGroup V) :
    t.toOpenPartialHomeomorph.symm (y, (t p₀).2 * g) ∈ orientedFrames o σ := by
  rw [t.symm_mul_eq_smul ht hy.1]
  exact (smul_mem_orientedFrames_iff hι hy.2).2 hg

open scoped Classical in
/-- The restriction of an equivariant trivialization `t` of the orthonormal frame bundle to the
positively oriented frames, through a positively oriented frame `p₀`. Its base set consists of the
points `y` of the base set of `t` where the frame `t⁻¹ (y, g₀)`, with `g₀ = (t p₀).2`, is
positively oriented; there it sends a positively oriented frame `p` to
`(p.proj, g₀⁻¹ * (t p).2)` in the special orthogonal group. -/
def restrictOrientedFrames :
    Trivialization (specialOrthogonalGroup V)
      (fun p : orientedFrames o σ ↦ (p : OrthonormalFrameBundle F E V).proj) where
  toFun p := ((p : OrthonormalFrameBundle F E V).proj,
    if h : (t p₀).2⁻¹ * (t p).2 ∈ specialOrthogonalGroup V then ⟨_, h⟩ else 1)
  invFun q :=
    if h : t.toOpenPartialHomeomorph.symm (q.1, (t p₀).2 * q.2) ∈ orientedFrames o σ then
      ⟨_, h⟩
    else ⟨p₀, hp₀⟩
  source := {p | (p : OrthonormalFrameBundle F E V).proj ∈ t.orientedBaseSet σ o p₀}
  target := t.orientedBaseSet σ o p₀ ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' q hq := by
    rw [dite_eq_left (t.symm_mul_mem_orientedFrames hι ht hq.1 q.2.2)]
    simp only [mem_ofPred_eq, t.proj_symm_apply' hq.1.1]
    exact hq.1
  left_inv' p hp := by
    have hp' := t.inv_mul_mem_specialOrthogonalGroup hι ht p.2 hp
    -- Multiplying back by `(t p₀).2` recovers the fibre coordinate of `p`.
    have hsymm : t.toOpenPartialHomeomorph.symm
        ((p : OrthonormalFrameBundle F E V).proj, (t p₀).2 * ((t p₀).2⁻¹ * (t p).2)) = p := by
      rw [mul_inv_cancel_left]
      exact t.symm_apply_mk_proj (t.mem_source.2 hp.1)
    have hmem : t.toOpenPartialHomeomorph.symm
        ((p : OrthonormalFrameBundle F E V).proj, (t p₀).2 * ((t p₀).2⁻¹ * (t p).2)) ∈
          orientedFrames o σ := by
      rw [hsymm]
      exact p.2
    simp only [dite_eq_left hp']
    rw [dite_eq_left hmem]
    exact Subtype.ext hsymm
  right_inv' q hq := by
    rw [dite_eq_left (t.symm_mul_mem_orientedFrames hι ht hq.1 q.2.2)]
    -- The fibre coordinate of `t⁻¹ (y, (t p₀).2 * g)` is `(t p₀).2 * g`.
    have h2 : (t p₀).2⁻¹ * (t (t.toOpenPartialHomeomorph.symm (q.1, (t p₀).2 * q.2))).2 =
        q.2 := by
      rw [t.apply_symm_apply' hq.1.1, inv_mul_cancel_left]
    refine Prod.ext (t.proj_symm_apply' hq.1.1) ?_
    dsimp only
    have hq2 : (t p₀).2⁻¹ * (t (t.toOpenPartialHomeomorph.symm (q.1, (t p₀).2 * q.2))).2 ∈
        specialOrthogonalGroup V := by
      rw [h2]
      exact q.2.2
    rw [dite_eq_left hq2]
    exact Subtype.ext h2
  open_source := (t.isOpen_orientedBaseSet hι).preimage
    (continuous_proj.comp continuous_subtype_val)
  open_target := (t.isOpen_orientedBaseSet hι).prod isOpen_univ
  continuousOn_toFun := by
    refine (continuous_proj.comp continuous_subtype_val).continuousOn.prodMk ?_
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : ContinuousOn (fun p : orientedFrames o σ ↦ (t p).2)
        {p | (p : OrthonormalFrameBundle F E V).proj ∈ t.orientedBaseSet σ o p₀} := by
      have h : ContinuousOn (fun p : orientedFrames o σ ↦ t p)
          {p | (p : OrthonormalFrameBundle F E V).proj ∈ t.orientedBaseSet σ o p₀} :=
        t.continuousOn_toFun.comp continuous_subtype_val.continuousOn
          fun p hp ↦ t.mem_source.2 hp.1
      exact continuous_snd.comp_continuousOn h
    refine ((continuous_const.mul hc.domRestrict).subtype_mk
      fun p ↦ t.inv_mul_mem_specialOrthogonalGroup hι ht p.1.2 p.2).congr fun p ↦ ?_
    simp only [domRestrict_apply,
      dite_eq_left (t.inv_mul_mem_specialOrthogonalGroup hι ht p.1.2 p.2)]
    rfl
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : ContinuousOn
        (fun q : B × specialOrthogonalGroup V ↦
          t.toOpenPartialHomeomorph.symm (q.1, (t p₀).2 * q.2))
        (t.orientedBaseSet σ o p₀ ×ˢ univ) :=
      t.toOpenPartialHomeomorph.continuousOn_symm.comp
        (continuous_fst.prodMk (continuous_const.mul
          (continuous_subtype_val.comp continuous_snd))).continuousOn
        fun q hq ↦ t.mem_target.2 hq.1.1
    refine (hc.domRestrict.subtype_mk
      fun q ↦ t.symm_mul_mem_orientedFrames hι ht q.2.1 q.1.2.2).congr fun q ↦ ?_
    simp only [domRestrict_apply, dite_eq_left (t.symm_mul_mem_orientedFrames hι ht q.2.1 q.1.2.2)]
  baseSet := t.orientedBaseSet σ o p₀
  open_baseSet := t.isOpen_orientedBaseSet hι
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

open scoped Classical in
private theorem restrictOrientedFrames_apply (p : orientedFrames o σ) :
    t.restrictOrientedFrames hι ht hp₀ p = ((p : OrthonormalFrameBundle F E V).proj,
      if h : (t p₀).2⁻¹ * (t p).2 ∈ specialOrthogonalGroup V then ⟨_, h⟩ else 1) :=
  rfl

open scoped Classical in
private theorem restrictOrientedFrames_symm_apply (q : B × specialOrthogonalGroup V) :
    (t.restrictOrientedFrames hι ht hp₀).toOpenPartialHomeomorph.symm q =
      if h : t.toOpenPartialHomeomorph.symm (q.1, (t p₀).2 * q.2) ∈ orientedFrames o σ then
        ⟨_, h⟩
      else ⟨p₀, hp₀⟩ :=
  rfl

/-- The base set of `t.restrictOrientedFrames` consists of the points `y` of the base set of `t`
where the frame `t⁻¹ (y, (t p₀).2)` is positively oriented. -/
theorem mem_baseSet_restrictOrientedFrames_iff {y : B} :
    y ∈ (t.restrictOrientedFrames hι ht hp₀).baseSet ↔
      y ∈ t.baseSet ∧ t.toOpenPartialHomeomorph.symm (y, (t p₀).2) ∈ orientedFrames o σ :=
  Iff.rfl

/-- The base set of `t.restrictOrientedFrames` contains the base point of `p₀`. -/
theorem mem_baseSet_restrictOrientedFrames (h₀ : p₀.proj ∈ t.baseSet) :
    p₀.proj ∈ (t.restrictOrientedFrames hι ht hp₀).baseSet := by
  rw [mem_baseSet_restrictOrientedFrames_iff, t.symm_apply_mk_proj (t.mem_source.2 h₀)]
  exact ⟨h₀, hp₀⟩

/-- Over its base set, the inverse of `t.restrictOrientedFrames` sends `(y, g)` to the frame
`t⁻¹ (y, (t p₀).2 * g)`. -/
theorem coe_restrictOrientedFrames_symm_apply {y : B}
    (hy : y ∈ (t.restrictOrientedFrames hι ht hp₀).baseSet) (g : specialOrthogonalGroup V) :
    ((t.restrictOrientedFrames hι ht hp₀).toOpenPartialHomeomorph.symm (y, g) :
      OrthonormalFrameBundle F E V) = t.toOpenPartialHomeomorph.symm (y, (t p₀).2 * g) := by
  rw [restrictOrientedFrames_symm_apply, dite_eq_left (t.symm_mul_mem_orientedFrames hι ht hy g.2)]

/-- Over its base set, `t.restrictOrientedFrames` reads a positively oriented frame `p` as
`(t p₀).2⁻¹ * (t p).2`. -/
theorem coe_restrictOrientedFrames_snd {p : orientedFrames o σ}
    (hp : (p : OrthonormalFrameBundle F E V).proj ∈ (t.restrictOrientedFrames hι ht hp₀).baseSet) :
    (((t.restrictOrientedFrames hι ht hp₀ p).2 : specialOrthogonalGroup V) :
      unitary (V →L[ℝ] V)) = (t p₀).2⁻¹ * (t p).2 := by
  rw [restrictOrientedFrames_apply,
    dite_eq_left (t.inv_mul_mem_specialOrthogonalGroup hι ht p.2 hp)]

/-- Over its base set, `t.restrictOrientedFrames` is equivariant: it intertwines the right action
of the special orthogonal group on positively oriented frames with right multiplication. -/
theorem restrictOrientedFrames_smul {p q : orientedFrames o σ} (g : specialOrthogonalGroup V)
    (hq : (q : OrthonormalFrameBundle F E V) = op (g : unitary (V →L[ℝ] V)) • p)
    (hp : (p : OrthonormalFrameBundle F E V).proj ∈ (t.restrictOrientedFrames hι ht hp₀).baseSet) :
    t.restrictOrientedFrames hι ht hp₀ q =
      ((t.restrictOrientedFrames hι ht hp₀ p).1, (t.restrictOrientedFrames hι ht hp₀ p).2 * g) := by
  have hq' : (q : OrthonormalFrameBundle F E V).proj ∈
      (t.restrictOrientedFrames hι ht hp₀).baseSet := by
    rwa [hq, proj_smul]
  refine Prod.ext ?_ (Subtype.ext ?_)
  · rw [Trivialization.coe_fst' _ hq', Trivialization.coe_fst' _ hp, hq, proj_smul]
  rw [Subgroup.coe_mul, coe_restrictOrientedFrames_snd hι t ht hp₀ hq',
    coe_restrictOrientedFrames_snd hι t ht hp₀ hp, hq, ht, mul_assoc]

end Bundle.Trivialization

namespace TauCeti.OrthonormalFrameBundle

variable [IsContinuousRiemannianBundle F E] [Fintype ι] [Nonempty ι] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ V]

/-- When `card ι` is positive and equal to the dimension of `V` and of the model fibre, the
positively oriented frames are locally trivial with fibre the special orthogonal group of `V`, by
trivializations equivariant for the right action. -/
theorem exists_trivialization_orientedFrames (hι : Fintype.card ι = finrank ℝ V)
    (hF : Fintype.card ι = finrank ℝ F) (o : Orientation ℝ V ι)
    (σ : VectorBundleOrientation F E ι) (x : B) :
    ∃ t : Trivialization (specialOrthogonalGroup V)
        (fun p : orientedFrames o σ ↦ (p : OrthonormalFrameBundle F E V).proj),
      x ∈ t.baseSet ∧ ∀ (g : specialOrthogonalGroup V) (p q : orientedFrames o σ),
        (q : OrthonormalFrameBundle F E V) = op (g : unitary (V →L[ℝ] V)) • p →
        (p : OrthonormalFrameBundle F E V).proj ∈ t.baseSet →
        t q = ((t p).1, (t p).2 * g) := by
  obtain ⟨t, hx, ht⟩ := exists_trivialization (E := E) (V := V) (hι.symm.trans hF) x
  obtain ⟨p₀, hp₀, rfl⟩ := exists_mem_orientedFrames_proj_eq hι hF o σ x
  exact ⟨t.restrictOrientedFrames hι ht hp₀, t.mem_baseSet_restrictOrientedFrames hι ht hp₀ hx,
    fun g _ _ hq hp ↦ t.restrictOrientedFrames_smul hι ht hp₀ g hq hp⟩

end TauCeti.OrthonormalFrameBundle
