/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Associated.Basic

/-!
# Pullback of an associated bundle

The bundle associated with a pullback principal bundle is canonically homeomorphic to the
pullback of its associated bundle. The comparison sends `[p,v]` over `x` to the same class
`[p,v]` over `f x`, regarded as a point of the pullback fibre. It preserves the base point
and agrees with the pullback trivializations. No linear structure on the model fibre is needed.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*,
  §§10.7 and 10.11.
-/

public section

noncomputable section

open Bundle Set Topology

namespace TauCeti.AssociatedBundle

variable {G B B' F : Type*} [TopologicalSpace B] [TopologicalSpace B']
  [Group G] [TopologicalSpace G] {P : B → Type*}
  [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, Nonempty (P b)]
  [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [TopologicalSpace F] [MulAction G F] [ContinuousSMul G F]
  {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] (f : K)

/-- The fibrewise comparison between associating after pullback and pulling back after
associating. On classes it sends `[p,v]` to `[p,v]`. -/
def pullbackEquiv (x : B') :
    AssociatedBundle G ((f : B' → B) *ᵖ P) F x ≃
      ((f : B' → B) *ᵖ (AssociatedBundle G P F)) x :=
  let p : P (f x) := (FiberBundle.homeomorphAt G P (f x)).symm 1
  (Equiv.ofBijective (mk G (P := (f : B' → B) *ᵖ P) (F := F) p)
      (mk_bijective (G := G) (P := (f : B' → B) *ᵖ P) (F := F) p)).symm.trans
    (Equiv.ofBijective (mk G (P := P) (F := F) p) (mk_bijective (G := G) (P := P) (F := F) p))

/-- The pullback comparison preserves associated classes. -/
@[simp]
theorem pullbackEquiv_mk (x : B') (p : P (f x)) (v : F) :
    pullbackEquiv (G := G) (P := P) (F := F) f x (mk G (P := (f : B' → B) *ᵖ P) p v) =
      mk G (P := P) (F := F) p v := by
  let q : ((f : B' → B) *ᵖ P) x := (FiberBundle.homeomorphAt G P (f x)).symm 1
  obtain ⟨w, hw⟩ := (mk_bijective (G := G) (P := (f : B' → B) *ᵖ P) (F := F) q).surjective
    (mk G (P := (f : B' → B) *ᵖ P) p v)
  have horig : mk G (P := P) q w = mk G (P := P) p v := by
    apply mk_eq_mk_iff.mpr
    have hpull := (mk_eq_mk_iff (G := G) (P := (f : B' → B) *ᵖ P)).mp hw
    exact hpull.trans (congrArg (· • v) (PrincipalBundle.division_pullback f q p))
  rw [← hw, ← horig]
  exact congrArg (mk G (P := P) q)
    ((Equiv.ofBijective (mk G (P := (f : B' → B) *ᵖ P) q)
      (mk_bijective (G := G) (P := (f : B' → B) *ᵖ P) (F := F) q)).symm_apply_apply w)

/-- The inverse pullback comparison preserves associated classes. -/
@[simp]
theorem pullbackEquiv_symm_mk (x : B') (p : P (f x)) (v : F) :
    (pullbackEquiv (G := G) (P := P) (F := F) f x).symm (mk G (P := P) (F := F) p v) =
      mk G (P := (f : B' → B) *ᵖ P) p v :=
  (pullbackEquiv f x).symm_apply_eq.mpr (pullbackEquiv_mk f x p v).symm

/-- In associated charts the pullback comparison reads the original chart at the image
base point. -/
theorem trivializationAt_pullbackEquiv_snd {x₀ x : B'}
    (hx : f x ∈ (trivializationAt G P (f x₀)).baseSet)
    (v : AssociatedBundle G ((f : B' → B) *ᵖ P) F x) :
    (trivializationAt F (AssociatedBundle G ((f : B' → B) *ᵖ P) F) x₀ ⟨x, v⟩).2 =
      (trivializationAt F (AssociatedBundle G P F) (f x₀)
        ⟨f x, pullbackEquiv f x v⟩).2 := by
  let p : ((f : B' → B) *ᵖ P) x := (FiberBundle.homeomorphAt G P (f x)).symm 1
  obtain ⟨w, rfl⟩ := (mk_bijective (G := G) (P := (f : B' → B) *ᵖ P) (F := F) p).surjective v
  rw [pullbackEquiv_mk,
    trivializationAt_mk_snd (G := G) (P := (f : B' → B) *ᵖ P) (b' := x₀) (b := x) hx p w,
    trivializationAt_mk_snd (G := G) (P := P) hx p w]
  rw [Pullback.trivializationAt_snd, Pullback.lift_mk]

/-- Associating commutes with pullback, as a homeomorphism of the native total spaces. -/
def pullbackHomeomorph :
    TotalSpace F (AssociatedBundle G ((f : B' → B) *ᵖ P) F) ≃ₜ
      TotalSpace F ((f : B' → B) *ᵖ (AssociatedBundle G P F)) where
  toFun z := ⟨z.proj, pullbackEquiv f z.proj z.2⟩
  invFun z := ⟨z.proj, (pullbackEquiv f z.proj).symm z.2⟩
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by
    apply Pullback.continuous_iff.mpr
    refine ⟨FiberBundle.continuous_proj F _, ?_⟩
    have hquot := (isOpenQuotientMap_totalSpaceMk_mk G ((f : B' → B) *ᵖ P) F).isQuotientMap
    apply hquot.continuous_iff.mpr
    convert Continuous.totalSpaceMk_associatedBundleMk (G := G) (P := P)
      ((Pullback.continuous_lift G P f).comp
        (continuous_fst : Continuous (Prod.fst : TotalSpace G ((f : B' → B) *ᵖ P) × F → _)))
      continuous_snd using 1
    funext ⟨⟨x, p⟩, v⟩
    exact congrArg (TotalSpace.mk (f x)) (pullbackEquiv_mk f x p v)
  continuous_invFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply (FiberBundle.continuousAt_totalSpace F _).mpr
    refine ⟨(Pullback.continuous_proj F (AssociatedBundle G P F) f).continuousAt, ?_⟩
    have hcoord := ((trivializationAt F (AssociatedBundle G P F) (f z.proj)).continuousAt
      (by simpa only [Trivialization.mem_source, baseSet_trivializationAt, Pullback.lift_proj]
        using mem_baseSet_trivializationAt G P (f z.proj))).comp
        (Pullback.continuous_lift F (AssociatedBundle G P F) f).continuousAt
    refine hcoord.snd.congr_of_eventuallyEq ?_
    filter_upwards [(((map_continuous f).comp
      (Pullback.continuous_proj F (AssociatedBundle G P F) f)).continuousAt)
      ((trivializationAt G P (f z.proj)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt G P (f z.proj)))] with y hy
    rcases y with ⟨y, v⟩
    exact (trivializationAt_pullbackEquiv_snd f hy
      ((pullbackEquiv f y).symm v)).trans
        (by simp only [Function.comp_apply,
          Pullback.lift_mk (F := F) (E := AssociatedBundle G P F) (f : B' → B) y v,
          Equiv.apply_symm_apply, Trivialization.coe_coe])

/-- The total-space comparison acts by the fibre comparison. -/
theorem pullbackHomeomorph_apply
    (z : TotalSpace F (AssociatedBundle G ((f : B' → B) *ᵖ P) F)) :
    pullbackHomeomorph (G := G) (P := P) (F := F) f z =
      ⟨z.proj, pullbackEquiv f z.proj z.2⟩ :=
  (rfl)

/-- The inverse total-space comparison acts by the inverse fibre comparison. -/
theorem pullbackHomeomorph_symm_apply
    (z : TotalSpace F ((f : B' → B) *ᵖ (AssociatedBundle G P F))) :
    (pullbackHomeomorph (G := G) (P := P) (F := F) f).symm z =
      ⟨z.proj, (pullbackEquiv f z.proj).symm z.2⟩ :=
  (rfl)

/-- The total-space comparison preserves the base point. -/
@[simp]
theorem pullbackHomeomorph_proj
    (z : TotalSpace F (AssociatedBundle G ((f : B' → B) *ᵖ P) F)) :
    (pullbackHomeomorph (G := G) (P := P) (F := F) f z).proj = z.proj :=
  (rfl)

/-- The total-space comparison sends an associated class to the same class in the pullback. -/
@[simp]
theorem pullbackHomeomorph_mk (x : B') (p : P (f x)) (v : F) :
    pullbackHomeomorph (G := G) (P := P) (F := F) f
      ⟨x, mk G (P := (f : B' → B) *ᵖ P) p v⟩ = ⟨x, mk G (P := P) (F := F) p v⟩ := by
  exact congrArg (TotalSpace.mk x) (pullbackEquiv_mk f x p v)

/-- The inverse total-space comparison also preserves the base point. -/
@[simp]
theorem pullbackHomeomorph_symm_proj
    (z : TotalSpace F ((f : B' → B) *ᵖ (AssociatedBundle G P F))) :
    ((pullbackHomeomorph (G := G) (P := P) (F := F) f).symm z).proj = z.proj :=
  (rfl)

/-- The inverse total-space comparison sends a class to the same class formed after pullback. -/
@[simp]
theorem pullbackHomeomorph_symm_mk (x : B') (p : P (f x)) (v : F) :
    (pullbackHomeomorph (G := G) (P := P) (F := F) f).symm
      ⟨x, mk G (P := P) (F := F) p v⟩ =
        ⟨x, mk G (P := (f : B' → B) *ᵖ P) p v⟩ :=
  (pullbackHomeomorph f).symm_apply_eq.mpr (pullbackHomeomorph_mk f x p v).symm

end TauCeti.AssociatedBundle
