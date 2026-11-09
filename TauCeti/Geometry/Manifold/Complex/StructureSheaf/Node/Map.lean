/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Node.LocalRing
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.InverseFunction

/-!
# Branchwise maps of analytic node rings

Two locally analytic maps between branch manifolds induce pullback on their branch-pair
local rings. For branches in the complex line, this pullback is an isomorphism exactly when
both branch derivatives are nonzero. The criterion gives an inverse of the whole local ring
map, rather than just an inverse on points or residue fields. It applies to local branch
coordinates without demanding entire extensions, and to a self-node as well as a node
joining different components.

The maps here preserve the two designated branches. No claim is made about maps contracting
a component or about recognizing arbitrary set-theoretic bijections as analytic isomorphisms.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), §3 (nodes and their branch maps).
-/

public noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.holomorphicStructureSheaf.nodeLocalRing

section Manifolds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℂ F G}
  {Y : Type} [TopologicalSpace Y] [ChartedSpace G Y]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℂ E' H'}
  {X' : Type} [TopologicalSpace X'] [ChartedSpace H' X']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners ℂ F' G'}
  {Y' : Type} [TopologicalSpace Y'] [ChartedSpace G' Y']
  {f : X → X'} {g : Y → Y'} {a : X} {b : Y}
  (hf : ∀ᶠ y in 𝓝 a, ContMDiffAt I I' ω f y)
  (hg : ∀ᶠ y in 𝓝 b, ContMDiffAt J J' ω g y)

/-- Pullback on a node ring by its two local analytic branch maps. -/
def pullback : nodeLocalRing I' J' (f a) (g b) →+* nodeLocalRing I J a b :=
  lift ((stalkPullback hf).comp (fst I' J' (f a) (g b)))
    ((stalkPullback hg).comp (snd I' J' (f a) (g b))) (fun s ↦ by simp)

/-- The first branch of a pulled-back node germ is its branch pullback. -/
@[simp]
theorem fst_pullback (s : nodeLocalRing I' J' (f a) (g b)) :
    fst I J a b (pullback hf hg s) = stalkPullback hf (fst I' J' (f a) (g b) s) := by
  simp only [pullback, fst_lift, RingHom.comp_apply]

/-- The second branch of a pulled-back node germ is its branch pullback. -/
@[simp]
theorem snd_pullback (s : nodeLocalRing I' J' (f a) (g b)) :
    snd I J a b (pullback hf hg s) = stalkPullback hg (snd I' J' (f a) (g b) s) := by
  simp only [pullback, snd_lift, RingHom.comp_apply]

/-- Branchwise pullback preserves the value at the node. -/
@[simp]
theorem eval_pullback (s : nodeLocalRing I' J' (f a) (g b)) :
    eval I J a b (pullback hf hg s) = eval I' J' (f a) (g b) s := by
  rw [← eval_fst, fst_pullback, eval_stalkPullback, eval_fst]

/-- Pullback on node rings is a local ring homomorphism. -/
instance isLocalHom_pullback : IsLocalHom (pullback hf hg) where
  map_nonunit s hs := (isUnit_iff s).mpr (by
    simpa only [eval_pullback] using ((isUnit_iff _).mp hs))

/-- The identity branch maps induce the identity on the node ring. -/
@[simp]
theorem pullback_id (a : X) (b : Y) :
    pullback (Eventually.of_forall fun _ ↦ contMDiffAt_id (I := I))
      (Eventually.of_forall fun _ ↦ contMDiffAt_id (I := J)) (a := a) (b := b) =
        RingHom.id _ := by
  ext s <;> simp

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℂ E'' H''}
  {X'' : Type} [TopologicalSpace X''] [ChartedSpace H'' X'']
  {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace ℂ F'']
  {G'' : Type*} [TopologicalSpace G''] {J'' : ModelWithCorners ℂ F'' G''}
  {Y'' : Type} [TopologicalSpace Y''] [ChartedSpace G'' Y'']

/-- Pullback by composite branch maps is the composite of the node pullbacks. -/
theorem pullback_comp {f' : X' → X''} {g' : Y' → Y''}
    (hf' : ∀ᶠ y in 𝓝 (f a), ContMDiffAt I' I'' ω f' y)
    (hg' : ∀ᶠ y in 𝓝 (g b), ContMDiffAt J' J'' ω g' y)
    (s : nodeLocalRing I'' J'' (f' (f a)) (g' (g b))) :
    pullback ((hf.and (hf.self_of_nhds.continuousAt.tendsto.eventually hf')).mono
        fun z hz ↦ hz.2.comp z hz.1)
      ((hg.and (hg.self_of_nhds.continuousAt.tendsto.eventually hg')).mono
        fun z hz ↦ hz.2.comp z hz.1) s = pullback hf hg (pullback hf' hg' s) := by
  apply ext
  · simp only [fst_pullback]
    exact stalkPullback_comp hf hf' _
  · simp only [snd_pullback]
    exact stalkPullback_comp hg hg' _

end Manifolds

variable {f g : ℂ → ℂ} {a b : ℂ} (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g b)

/-- A branchwise analytic node map is an isomorphism on local rings exactly when both
branch derivatives are nonzero. -/
theorem pullback_bijective_iff :
    Function.Bijective (pullback (eventually_contMDiffAt_of_analyticAt hf)
      (eventually_contMDiffAt_of_analyticAt hg)) ↔ deriv f a ≠ 0 ∧ deriv g b ≠ 0 := by
  constructor
  · intro h
    constructor
    · apply (stalkPullback_surjective_iff hf).mp
      intro u
      obtain ⟨s, hs⟩ := fst_surjective (I := 𝓘(ℂ)) (J := 𝓘(ℂ)) (q := b) u
      obtain ⟨t, rfl⟩ := h.2 s
      exact ⟨fst 𝓘(ℂ) 𝓘(ℂ) (f a) (g b) t, by simpa using hs⟩
    · apply (stalkPullback_surjective_iff hg).mp
      intro u
      obtain ⟨s, hs⟩ := snd_surjective (I := 𝓘(ℂ)) (J := 𝓘(ℂ)) (p := a) u
      obtain ⟨t, rfl⟩ := h.2 s
      exact ⟨snd 𝓘(ℂ) 𝓘(ℂ) (f a) (g b) t, by simpa using hs⟩
  · rintro ⟨hf0, hg0⟩
    have hF := (stalkPullback_bijective_iff hf).mpr hf0
    have hG := (stalkPullback_bijective_iff hg).mpr hg0
    constructor
    · intro s t h
      exact ext (hF.1 (by simpa using congrArg (fst 𝓘(ℂ) 𝓘(ℂ) a b) h))
        (hG.1 (by simpa using congrArg (snd 𝓘(ℂ) 𝓘(ℂ) a b) h))
    · intro s
      obtain ⟨u, hu⟩ := hF.2 (fst 𝓘(ℂ) 𝓘(ℂ) a b s)
      obtain ⟨v, hv⟩ := hG.2 (snd 𝓘(ℂ) 𝓘(ℂ) a b s)
      have he : holomorphicStructureSheaf.eval 𝓘(ℂ) ℂ (f a) u =
          holomorphicStructureSheaf.eval 𝓘(ℂ) ℂ (g b) v := by
        rw [← eval_stalkPullback (eventually_contMDiffAt_of_analyticAt hf),
          ← eval_stalkPullback (eventually_contMDiffAt_of_analyticAt hg), hu, hv,
          eval_fst, eval_snd]
      exact ⟨mk u v he, ext (by simpa using hu) (by simpa using hv)⟩

/-- The local-ring isomorphism induced by two unramified branch maps. -/
def pullbackEquiv (hf0 : deriv f a ≠ 0) (hg0 : deriv g b ≠ 0) :
    nodeLocalRing 𝓘(ℂ) 𝓘(ℂ) (f a) (g b) ≃+* nodeLocalRing 𝓘(ℂ) 𝓘(ℂ) a b :=
  RingEquiv.ofBijective (pullback (eventually_contMDiffAt_of_analyticAt hf)
    (eventually_contMDiffAt_of_analyticAt hg)) ((pullback_bijective_iff hf hg).mpr ⟨hf0, hg0⟩)

/-- The isomorphism agrees with the actual pullback of node germs. -/
@[simp]
theorem pullbackEquiv_apply (hf0 : deriv f a ≠ 0) (hg0 : deriv g b ≠ 0)
    (s : nodeLocalRing 𝓘(ℂ) 𝓘(ℂ) (f a) (g b)) :
    pullbackEquiv hf hg hf0 hg0 s = pullback (eventually_contMDiffAt_of_analyticAt hf)
      (eventually_contMDiffAt_of_analyticAt hg) s := (rfl)

end TauCeti.holomorphicStructureSheaf.nodeLocalRing
