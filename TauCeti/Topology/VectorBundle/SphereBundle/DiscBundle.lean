/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalTrivialization
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic

/-!
# Local triviality of unit disc bundles

For a real vector bundle `E → B` with normed fibres, `TauCeti.discBundle F E` is the unit disc
subset of `TotalSpace F E` (defined in `TauCeti.Topology.VectorBundle.SphereBundle.Basic`). This
file restricts norm-preserving local trivializations of `E` to local trivializations of
`discBundleProj F E : D(E) → B` with model fibre `closedBall (0 : F) 1`:

* `Bundle.Trivialization.discBundle`: restriction of a norm-preserving local trivialization of `E`
  to a local trivialization of `discBundleProj F E` with fibre `closedBall (0 : F) 1`;
* `TauCeti.exists_trivialization_discBundleProj`: for a finite-rank continuous Riemannian vector
  bundle, `discBundleProj F E` is locally trivial with fibre `closedBall (0 : F) 1`.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §2 (Euclidean metrics on vector bundles), §12, and §18 (unit
  sphere and unit disc bundles).
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2.
* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 3.
-/

public section

noncomputable section

open Bundle Filter Metric Set Topology

universe w

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E]

open Classical in
/-- Restrict a fibrewise norm-preserving local trivialization `e` of `E` to a local trivialization
of `discBundleProj F E : D(E) → B` with model fibre `closedBall (0 : F) 1`. -/
def discBundle (e : Trivialization F (π F E))
    (he : ∀ b ∈ e.baseSet, ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖) :
    Trivialization (closedBall (0 : F) 1) (discBundleProj F E) where
  toFun v := (discBundleProj F E v,
    if hb : v.val.proj ∈ e.baseSet then
      ⟨(e v.val).2,
        mem_closedBall_zero_iff.2
          ((he v.val.proj hb v.val.snd).trans_le (mem_discBundle.1 v.property))⟩
    else ⟨0, mem_closedBall_self zero_le_one⟩)
  invFun p :=
    if hb : p.1 ∈ e.baseSet then
      ⟨e.toOpenPartialHomeomorph.symm (p.1, p.2.val), by
        have hproj : (e.toOpenPartialHomeomorph.symm (p.1, p.2.val)).proj = p.1 :=
          e.proj_symm_apply' hb
        have happ : e (e.toOpenPartialHomeomorph.symm (p.1, p.2.val)) = (p.1, p.2.val) :=
          e.apply_symm_apply (e.mem_target.2 hb)
        have hiso := he _ (hproj.symm ▸ hb) (e.toOpenPartialHomeomorph.symm (p.1, p.2.val)).snd
        rw [mem_discBundle, ← hiso, happ]
        exact mem_closedBall_zero_iff.1 p.2.property⟩
    else ⟨TotalSpace.mk' F p.1 0, by simp⟩
  source := discBundleProj F E ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' v hv := ⟨hv, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, discBundleProj_apply, dite_eq_left hp.1]
    exact (e.proj_symm_apply' hp.1).symm ▸ hp.1
  left_inv' v hv := by
    have hv' : (v : TotalSpace F E).proj ∈ e.baseSet := by
      simpa only [mem_preimage, discBundleProj_apply] using hv
    apply Subtype.ext
    dsimp only
    rw [discBundleProj_apply, dite_eq_left hv', dite_eq_left hv']
    exact e.symm_apply_mk_proj (e.mem_source.2 hv')
  right_inv' p hp := by
    ext
    · dsimp only
      rw [discBundleProj_apply, dite_eq_left hp.1]
      exact e.proj_symm_apply' hp.1
    · dsimp only
      rw [dite_eq_left hp.1, dite_eq_left (by rw [e.proj_symm_apply' hp.1]; exact hp.1)]
      dsimp only
      rw [e.apply_symm_apply (e.mem_target.2 hp.1)]
  open_source := e.open_baseSet.preimage (discBundleProj F E).continuous
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := by
    refine (discBundleProj F E).continuous.continuousOn.prodMk ?_
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (continuous_snd.comp_continuousOn <|
      e.continuousOn.comp continuous_subtypeVal.continuousOn fun v hv ↦
        e.mem_source.2 (by simpa only [mem_preimage, discBundleProj_apply] using hv)).congr
      fun v hv ↦ ?_
    have hv' : (v : TotalSpace F E).proj ∈ e.baseSet := by
      simpa only [mem_preimage, discBundleProj_apply] using hv
    dsimp only [Function.comp_apply]
    rw [dite_eq_left hv']
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (e.toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd)).continuousOn
      fun p (hp : p ∈ e.baseSet ×ˢ univ) ↦ e.mem_target.2 hp.1).congr fun p hp ↦ ?_
    dsimp only [Function.comp_apply]
    rw [dite_eq_left hp.1]
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem discBundle_baseSet (e : Trivialization F (π F E))
    (he : ∀ b ∈ e.baseSet, ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖) :
    (e.discBundle he).baseSet = e.baseSet :=
  (rfl)

open Classical in
@[simp]
theorem coe_discBundle_apply_snd (e : Trivialization F (π F E))
    (he : ∀ b ∈ e.baseSet, ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖)
    {v : TauCeti.discBundle F E} (hv : (v : TotalSpace F E).proj ∈ e.baseSet) :
    ((e.discBundle he v).2 : F) = (e v.val).2 := by
  simp [discBundle, hv]

open Classical in
/-- Over its base set, the inverse chart of the disc bundle agrees with the inverse of `e`. -/
@[simp]
theorem coe_discBundle_symm_apply (e : Trivialization F (π F E))
    (he : ∀ b ∈ e.baseSet, ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖)
    {b : B} (hb : b ∈ e.baseSet) (w : closedBall (0 : F) 1) :
    ((e.discBundle he).toOpenPartialHomeomorph.symm (b, w) : TotalSpace F E) =
      e.toOpenPartialHomeomorph.symm (b, w.val) := by
  simp [discBundle, hb]

end Bundle.Trivialization

namespace TauCeti

section LocalTriviality

variable {B : Type w} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

/-- Around every point of the base, `discBundleProj F E : D(E) → B` has a local trivialization with
model fibre `closedBall (0 : F) 1`. -/
theorem exists_trivialization_discBundleProj (b : B) :
    ∃ e : Trivialization (closedBall (0 : F) 1) (discBundleProj F E), b ∈ e.baseSet := by
  obtain ⟨e, _, hb, hiso⟩ :=
    OrthonormalBasis.exists_orthonormal_trivialization (E := E) (stdOrthonormalBasis ℝ F) b
  exact ⟨e.discBundle hiso, hb⟩

end LocalTriviality

end TauCeti
