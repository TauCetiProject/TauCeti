/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Topology.CellularSet.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Separation.Connected
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.CellularSet.InverseSet
import TauCeti.Topology.Separation.InvFunOn
import TauCeti.Topology.Sphere.Shrink

/-!
# Both inverse sets of a map of a sphere with two inverse sets are cellular

Let `Sⁿ` be the unit sphere of a real inner product space of dimension `n + 1`, `n ≥ 2`, and let
`f : Sⁿ → Sⁿ` be a continuous surjection which is injective off the two fibres `A = f⁻¹(a)` and
`B = f⁻¹(c)`, `a ≠ c`: in M. Brown's terminology, `A` and `B` are the only *inverse sets* of `f`.
Then `B` (and symmetrically `A`) is cellular, modelled on any real normed space of dimension `n`
(`TauCeti.isCellularSet_preimage_singleton_of_injOn`). This is Theorem 4 of Brown's proof of the
generalized Schoenflies theorem. With the collapse of the outside of a bicollar onto two poles
(`TauCeti.IsBicollar.exists_collapse`) it shows that the two collapsed pieces are cellular, which
identifies the closures of the complementary domains of a bicollared sphere with cells (Brown's
Theorem 5).

Brown's proof reduces to his theorem on a single inverse set
(`TauCeti.isCellularSet_closedBall_inter_preimage`) by removing `A` with a push of the target.

* Choose a point `z` off `A ∪ B`. The inverse stereographic projection from `z` of a large ball is
  a closed cell `Q` of `Sⁿ`, missing `z` and containing `B` in its open cell.
* The point `f z` is not in `f(Q)`, since `f` is injective off `A ∪ B`. Pushing `f(Q)` away from
  `c` by a map `k`, continuous and injective off `f z` and the identity near `a`
  (`TauCeti.exists_continuousOn_injOn_mapsTo_sphere`), gives `g = f⁻¹ ∘ k ∘ f` off `A`, extended
  by the identity on `A`. The inverse of `f` off `A ∪ B` is continuous since `Sⁿ` is compact.
* On `Q` the map `g` is continuous, injective off `B`, and collapses `B` to the single point
  `f⁻¹(k c)`. So `B` is the only inverse set of `g` read on `Q`, hence cellular.

## Main results

* `TauCeti.isCellularSet_preimage_singleton_of_injOn`: **Brown's theorem on two inverse sets**: both
  inverse sets of a map of `Sⁿ` onto itself with exactly two inverse sets are cellular.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 4.
-/

public section

open Function Metric Module Set Filter Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A closed cell around a compact set.** Let `K` be a compact subset of the unit sphere of a
real inner product space of dimension `dim E + 1`, missing a point `z`. The inverse stereographic
projection from `z` of a large ball, parametrized by `E`, is a continuous injection `ψ : E → Sⁿ`
missing `z`, which carries the open unit ball over `K` and the unit sphere off `K`. -/
private theorem exists_cell (hEF : finrank ℝ F = finrank ℝ E + 1) {K : Set (sphere (0 : F) 1)}
    (hK : IsCompact K) {z : sphere (0 : F) 1} (hzK : z ∉ K) :
    ∃ ψ : E → sphere (0 : F) 1, Continuous ψ ∧ Injective ψ ∧ (∀ v, ψ v ≠ z) ∧
      K ⊆ ψ '' ball 0 1 ∧ Disjoint (ψ '' sphere 0 1) K := by
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  set φ := stereographic' (finrank ℝ E) z
  have hmem (u : EuclideanSpace ℝ (Fin (finrank ℝ E))) : u ∈ φ.target := by
    rw [stereographic'_target]
    trivial
  have hKs : K ⊆ φ.source := fun x hx ↦ by
    rw [stereographic'_source, mem_compl_singleton_iff]
    exact fun h ↦ hzK (h ▸ hx)
  -- `φ '' K` lies in a ball of radius `R ≥ 1`.
  obtain ⟨r, hr⟩ := (hK.image_of_continuousOn (φ.continuousOn.mono hKs)).isBounded.subset_ball 0
  set R := max r 1
  have hR : 0 < R := one_pos.trans_le (le_max_right r 1)
  set L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  set T := L.unitBallHomeomorph
  refine ⟨fun v ↦ φ.symm (R • T v),
    φ.continuousOn_symm.comp_continuous (by fun_prop) fun v ↦ hmem _, fun v w h ↦ ?_,
    fun v h ↦ ?_, fun x hx ↦ ⟨T.symm (R⁻¹ • φ x), ?_, ?_⟩, ?_⟩
  · exact T.injective (smul_right_injective _ hR.ne'
      (φ.symm.injOn (by simpa using hmem _) (by simpa using hmem _) h))
  · have := φ.map_target (hmem (R • T v))
    rw [stereographic'_source, mem_compl_singleton_iff] at this
    exact this h
  · have hx' : ‖φ x‖ < R := mem_ball_zero_iff.1 (hr (mem_image_of_mem φ hx)) |>.trans_le
      (le_max_left r 1)
    rw [mem_ball_zero_iff, L.norm_unitBallHomeomorph_symm_lt_one_iff, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 hR.le), inv_mul_lt_one₀ hR]
    exact hx'
  · simp only [T, Homeomorph.apply_symm_apply, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    exact φ.left_inv (hKs hx)
  · refine disjoint_left.2 ?_
    rintro _ ⟨v, hv, rfl⟩ hvK
    have hRv := mem_ball_zero_iff.1 (hr ⟨_, hvK, φ.right_inv (hmem (R • T v))⟩)
    rw [norm_smul, Real.norm_of_nonneg hR.le,
      L.norm_unitBallHomeomorph_eq_one_iff.2 (mem_sphere_zero_iff_norm.1 hv), mul_one] at hRv
    exact (le_max_left r 1).not_gt hRv

/-- **Brown's map.** Let `f` be a continuous surjection of the unit sphere `Sⁿ` onto itself,
injective off the fibres over two points `a ≠ c`, and let `Q` be a compact set containing
`f⁻¹(c)` whose image misses a point `p ≠ a`. There is a map `g` of `Sⁿ`, continuous at every point
of `Q`, injective on `Q \ f⁻¹(c)`, which sends exactly the points of `Q` in `f⁻¹(c)` to a single
point `y₀`. It is the identity on `f⁻¹(a)` and `f⁻¹ ∘ k ∘ f` elsewhere, for a push `k` of `f(Q)`
off `c` which is the identity near `a`. -/
private theorem exists_continuousAt_injOn_sdiff_preimage [FiniteDimensional ℝ F]
    {f : sphere (0 : F) 1 → sphere (0 : F) 1} (hf : Continuous f) (hfs : Surjective f)
    {a c : sphere (0 : F) 1} (hac : a ≠ c) (hinj : InjOn f (f ⁻¹' {a, c})ᶜ)
    {Q : Set (sphere (0 : F) 1)} (hQ : IsCompact Q) (hcQ : f ⁻¹' {c} ⊆ Q)
    {p : sphere (0 : F) 1} (hpa : p ≠ a) (hpQ : p ∉ f '' Q) :
    ∃ g : sphere (0 : F) 1 → sphere (0 : F) 1, ∃ y₀, (∀ x ∈ Q, ContinuousAt g x) ∧
      InjOn g (Q \ f ⁻¹' {c}) ∧ ∀ x ∈ Q, g x = y₀ ↔ f x = c := by
  classical
  have : Nonempty (sphere (0 : F) 1) := ⟨a⟩
  set U := (f ⁻¹' {a, c})ᶜ
  have hU {x : sphere (0 : F) 1} : x ∈ U ↔ f x ≠ a ∧ f x ≠ c := by simp [U]
  have hQp {x : sphere (0 : F) 1} (hx : x ∈ Q) : f x ≠ p := fun h ↦ hpQ ⟨x, hx, h⟩
  -- A push `k` of `f(Q)` off `c`, the identity near `a`.
  obtain ⟨k, hkc, hki, hkid, hkN⟩ := exists_continuousOn_injOn_mapsTo_sphere hpa.symm
    (hQ.image hf) hpQ (isOpen_compl_singleton.mem_nhds hac)
  have hka : k a = a := hkid.eq_of_nhds
  have hkQa {x : sphere (0 : F) 1} (hx : x ∈ Q) : k (f x) = a ↔ f x = a :=
    ⟨fun h ↦ hki (hQp hx) hpa.symm (h.trans hka.symm), fun h ↦ h ▸ hka⟩
  have hkQc {x : sphere (0 : F) 1} (hx : x ∈ Q) : k (f x) ≠ c := hkN (mem_image_of_mem f hx)
  -- The inverse of `f` off `f⁻¹(a) ∪ f⁻¹(c)`, which is continuous since `Sⁿ` is compact.
  have hfU {y : sphere (0 : F) 1} (hya : y ≠ a) (hyc : y ≠ c) : ∃ x ∈ U, f x = y := by
    obtain ⟨x, rfl⟩ := hfs y
    exact ⟨x, hU.2 ⟨hya, hyc⟩, rfl⟩
  have hinv : ContinuousOn (invFunOn f U) ({a, c} : Set (sphere (0 : F) 1))ᶜ := by
    refine (hf.continuousOn.continuousOn_invFunOn_image_of_isCompact isCompact_univ
      (subset_univ U) hinj (disjoint_left.2 ?_)).mono fun y hy ↦ ?_
    · rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
      exact hx' (by simpa only [U, mem_compl_iff, mem_preimage, hxx', not_not] using hx.2)
    · obtain ⟨x, hx, rfl⟩ := hfU (fun h ↦ hy (.inl h)) fun h ↦ hy (.inr h)
      exact mem_image_of_mem f hx
  have hinvU {y : sphere (0 : F) 1} (hya : y ≠ a) (hyc : y ≠ c) :
      invFunOn f U y ∈ U ∧ f (invFunOn f U y) = y :=
    ⟨invFunOn_mem (hfU hya hyc), invFunOn_eq (hfU hya hyc)⟩
  -- Brown's map: the identity on `f⁻¹(a)`, and `f⁻¹ ∘ k ∘ f` elsewhere.
  set g : sphere (0 : F) 1 → sphere (0 : F) 1 := fun x ↦
    if f x = a then x else invFunOn f U (k (f x))
  have hfg {x : sphere (0 : F) 1} (hx : x ∈ Q) : f (g x) = k (f x) := by
    by_cases hxa : f x = a
    · simp only [g, hxa, ↓reduceIte, hka]
    · simp only [g, hxa, ↓reduceIte]
      exact (hinvU (fun h ↦ hxa ((hkQa hx).1 h)) (hkQc hx)).2
  obtain ⟨xc, hxc⟩ := hfs c
  have hxcQ : xc ∈ Q := hcQ hxc
  have hy₀ : f (invFunOn f U (k c)) = k c :=
    (hinvU (fun h ↦ hac.symm (hxc.symm.trans ((hkQa hxcQ).1 (hxc.symm ▸ h))))
      (hxc ▸ hkQc hxcQ)).2
  refine ⟨g, invFunOn f U (k c), fun x hx ↦ ?_, fun x hx x' hx' h ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨W, hWk, hW, haW⟩ := _root_.eventually_nhds_iff.1 hkid
    by_cases hxW : f x ∈ W ∩ {c}ᶜ
    · -- Near a point mapped into `W`, away from `c`, the map `g` is the identity.
      refine continuousAt_id.congr (Filter.EventuallyEq.symm ?_)
      filter_upwards [hf.continuousAt.preimage_mem_nhds
        ((hW.inter isOpen_compl_singleton).mem_nhds hxW)] with x' hx'
      by_cases hx'a : f x' = a
      · simp only [g, hx'a, ↓reduceIte, id]
      · simp only [g, hx'a, ↓reduceIte, id]
        rw [show k (f x') = f x' from hWk _ hx'.1]
        exact hinj.leftInvOn_invFunOn (hU.2 ⟨hx'a, hx'.2⟩)
    · -- Elsewhere `g` is `f⁻¹ ∘ k ∘ f`, near a point mapped off `a`.
      have hxa : f x ≠ a := fun h ↦ hxW ⟨h ▸ haW, h ▸ hac⟩
      have hkx : k (f x) ∈ ({a, c} : Set (sphere (0 : F) 1))ᶜ := by
        rintro (h | h)
        exacts [hxa ((hkQa hx).1 h), hkQc hx h]
      have hkf : ContinuousAt (fun x' ↦ k (f x')) x :=
        (hkc.continuousAt (isOpen_compl_singleton.mem_nhds (hQp hx))).comp hf.continuousAt
      have hinvx : ContinuousAt (invFunOn f U) (k (f x)) :=
        hinv.continuousAt (((finite_singleton c).insert a).isClosed.isOpen_compl.mem_nhds hkx)
      refine (ContinuousAt.comp (f := fun x' ↦ k (f x')) (x := x) hinvx hkf).congr ?_
      filter_upwards [hf.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hxa)]
        with x' hx'
      simp only [g, comp_apply, show f x' ≠ a from hx', ↓reduceIte]
  · -- `f ∘ g = k ∘ f` on `Q`, and `k` is injective off `p`.
    have hffx : f x = f x' := hki (hQp hx.1) (hQp hx'.1)
      (by rw [← hfg hx.1, ← hfg hx'.1, h])
    by_cases hxa : f x = a
    · simpa only [g, hxa, ← hffx, ↓reduceIte] using h
    · exact hinj (hU.2 ⟨hxa, hx.2⟩) (hU.2 ⟨hffx ▸ hxa, hffx ▸ hx.2⟩) hffx
  · refine ⟨fun h ↦ (hki (hQp hxcQ) (hQp hx) ?_).symm.trans hxc, fun h ↦ ?_⟩
    · rw [hxc, ← hy₀, ← h, hfg hx]
    · simp only [g, h, hac.symm, ↓reduceIte]

/-- **Brown's theorem on two inverse sets.** Let `E` be a real normed space of dimension `n ≥ 2`,
and let `f` be a continuous surjection of the unit sphere `Sⁿ` of a real inner product space of
dimension `n + 1` onto itself. Suppose that `f` is injective off the two fibres `f⁻¹(a)` and
`f⁻¹(c)`, `a ≠ c`, so that they are the only inverse sets of `f`. Then `f⁻¹(c)` is cellular; by
symmetry, so is `f⁻¹(a)`. -/
theorem isCellularSet_preimage_singleton_of_injOn (hn : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {f : sphere (0 : F) 1 → sphere (0 : F) 1}
    (hf : Continuous f) (hfs : Surjective f) {a c : sphere (0 : F) 1} (hac : a ≠ c)
    (hinj : InjOn f (f ⁻¹' {a, c})ᶜ) : IsCellularSet E (f ⁻¹' {c}) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  set B := f ⁻¹' {c}
  -- A point `z` off both inverse sets: the sphere is connected with two antipodal points, so it is
  -- infinite.
  have hS : (sphere (0 : F) 1).Infinite := IsPreconnected.infinite_of_nontrivial
    (isPreconnected_sphere (E := F)
      (by rw [← finrank_eq_rank]; exact_mod_cast (by omega : 1 < finrank ℝ F)) 0 1)
    ⟨a, a.2, ↑(-a), (-a).2, Subtype.coe_injective.ne (ne_neg_of_mem_unit_sphere ℝ a)⟩
  obtain ⟨w, hw, hwac⟩ := (hS.sdiff (toFinite {(a : F), (c : F)})).nonempty
  obtain ⟨z, hz⟩ := hfs ⟨w, hw⟩
  have hza : f z ≠ a := fun h ↦ hwac (.inl (by rw [← h, hz]))
  have hzc : f z ≠ c := fun h ↦ hwac (.inr (by rw [← h, hz]; rfl))
  -- A closed cell `Q` missing `z`, with `B` in its open cell; `f z` is not in `f(Q)`.
  obtain ⟨ψ, hψc, hψi, hψz, hBψ, hψS⟩ :=
    exists_cell (E := E) hEF (isClosed_singleton.preimage hf).isCompact (K := B) hzc
  set Q := ψ '' closedBall (0 : E) 1
  have hBQ : B ⊆ Q := hBψ.trans (image_mono ball_subset_closedBall)
  have hzQ : f z ∉ f '' Q := by
    rintro ⟨_, ⟨v, -, rfl⟩, h⟩
    refine hψz v (hinj ?_ ?_ h)
    · rw [mem_compl_iff, mem_preimage, h]
      rintro (h' | h') <;> [exact hza h'; exact hzc h']
    · rintro (h' | h') <;> [exact hza h'; exact hzc h']
  obtain ⟨g, y₀, hgc, hgi, hfib⟩ := exists_continuousAt_injOn_sdiff_preimage hf hfs hac hinj
    ((isCompact_closedBall 0 1).image hψc) hBQ hza hzQ
  -- So `B` is the only inverse set of `g ∘ ψ` on the closed ball.
  have hψQ {v : E} (hv : v ∈ closedBall 0 1) : ψ v ∈ Q := mem_image_of_mem ψ hv
  have hcell := isCellularSet_closedBall_inter_preimage (f := g ∘ ψ) (y := y₀) hn hEF
    (fun v hv ↦ ((hgc _ (hψQ hv)).comp hψc.continuousAt).continuousWithinAt)
    (fun v hv w hw h ↦ hψi (hgi ⟨hψQ hv.1, fun h' ↦ hv.2 ((hfib _ (hψQ hv.1)).2 h')⟩
      ⟨hψQ hw.1, fun h' ↦ hw.2 ((hfib _ (hψQ hw.1)).2 h')⟩ h))
    (fun ⟨v, hv, h⟩ ↦ disjoint_left.1 hψS (mem_image_of_mem ψ hv)
      ((hfib _ (hψQ (sphere_subset_closedBall hv))).1 h))
    (by
      obtain ⟨xc, hxc⟩ := hfs c
      obtain ⟨v, hv, hvc⟩ := hBψ hxc
      refine ⟨v, ball_subset_closedBall hv, (hfib _ (hψQ (ball_subset_closedBall hv))).2 ?_⟩
      rw [hvc]
      exact hxc)
  have hX : closedBall (0 : E) 1 ∩ (g ∘ ψ) ⁻¹' {y₀} = closedBall 0 1 ∩ ψ ⁻¹' B := by
    ext v
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, comp_apply, B]
    exact and_congr_right fun hv ↦ hfib _ (hψQ hv)
  rw [hX] at hcell
  have hXb : closedBall (0 : E) 1 ∩ ψ ⁻¹' B ⊆ ball 0 1 := fun v hv ↦ by
    rw [← closedBall_sdiff_sphere]
    exact ⟨hv.1, fun hs ↦ disjoint_left.1 hψS (mem_image_of_mem ψ hs) hv.2⟩
  have himg : ψ '' (closedBall (0 : E) 1 ∩ ψ ⁻¹' B) = B := by
    rw [image_inter_preimage, inter_eq_right.2 hBQ]
  exact himg ▸ hcell.image hXb hψc.continuousOn hψi.injOn

end TauCeti
