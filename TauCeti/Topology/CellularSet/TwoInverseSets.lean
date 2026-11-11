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
import TauCeti.Topology.CellularSet.InverseSet
import TauCeti.Topology.Separation.InvFunOn
import TauCeti.Topology.Sphere.Shrink

/-!
# The two inverse sets of a map of a sphere onto itself are cellular

Let `f` be a continuous surjection of the unit sphere `Sⁿ` of a real inner product space of
dimension `n + 1 ≥ 3` onto itself, and let `a ≠ b` be two points such that `f` is injective off
`f⁻¹{a, b}`. Then `f⁻¹(a)` and `f⁻¹(b)` are cellular
(`TauCeti.isCellularSet_preimage_singleton_of_injOn`). This is Theorem 4 of M. Brown's proof of
the generalized Schoenflies theorem, where `f⁻¹(a)` and `f⁻¹(b)` are the only two inverse sets
of `f`. The statement does not ask the fibres to have more than one point.

The proof reduces to Brown's theorem on the only inverse set of a map of a cell into `Sⁿ`
(`TauCeti.isCellularSet_closedBall_inter_preimage`). Choose a point `x₀` off `f⁻¹{a, b}`; it
exists because `Sⁿ` is connected. In the stereographic chart from `x₀`, a large closed ball `Q`
contains `f⁻¹{a, b}` in its interior, and `p = f x₀` is not in `f(Q)`. A squeeze `k` of the sphere
which is the identity near `b`, continuous and injective off `p`, carries `f(Q)` off `a`
(`TauCeti.exists_continuousOn_injOn_mapsTo_sphere`). The map `g` of `Q` which is the identity on
`f⁻¹(b)` and `f⁻¹ ∘ k ∘ f` elsewhere is then well defined and continuous, since `f` restricts to a
homeomorphism off `f⁻¹{a, b}`, and its only inverse set is `f⁻¹(a)`, which it sends to the single
point `f⁻¹(k a)`.

## Main results

* `TauCeti.isCellularSet_preimage_singleton_of_injOn`: **Brown's theorem on two inverse sets**.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 4.
-/

public section

open Function Metric Module Set Filter Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A continuous injection `ψ` of `E` into the sphere, missing a point `x₀` off a compact set `K`,
which maps the open unit ball onto a set containing `K`: the inverse of the stereographic chart at
`x₀`, read through a linear identification of `E` with Euclidean space and rescaled. -/
private theorem exists_continuous_injective_subset_image_ball
    (hEF : finrank ℝ F = finrank ℝ E + 1) {x₀ : sphere (0 : F) 1} {K : Set (sphere (0 : F) 1)}
    (hK : IsCompact K) (hx₀ : x₀ ∉ K) :
    ∃ ψ : E → sphere (0 : F) 1, Continuous ψ ∧ Injective ψ ∧ x₀ ∉ range ψ ∧
      K ⊆ ψ '' ball 0 1 := by
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  set φ := stereographic' (finrank ℝ E) x₀
  have hsrc : φ.source = {x₀}ᶜ := stereographic'_source x₀
  have htgt : φ.target = univ := stereographic'_target x₀
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hKs : K ⊆ φ.source := fun x hx ↦ by
    rw [hsrc]
    exact fun h ↦ hx₀ (h ▸ hx)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun x ↦ L.symm (φ x)) (L.symm.continuous.comp_continuousOn (φ.continuousOn.mono hKs))
  set R := max C 0 + 1
  have hR : 0 < R := by positivity
  have hsymm : Continuous φ.symm := continuousOn_univ.1 (htgt ▸ φ.continuousOn_symm)
  refine ⟨fun z ↦ φ.symm (L (R • z)), hsymm.comp (L.continuous.comp (continuous_const_smul R)),
    fun z z' h ↦ ?_, ?_, fun x hx ↦ ⟨R⁻¹ • L.symm (φ x), ?_, ?_⟩⟩
  · have := φ.symm.injOn (by rw [φ.symm_source, htgt]; trivial)
      (by rw [φ.symm_source, htgt]; trivial) h
    exact smul_right_injective E hR.ne' (L.injective this)
  · rintro ⟨z, hz⟩
    have := φ.map_target (x := L (R • z)) (by rw [htgt]; trivial)
    dsimp only at hz
    rw [hz, hsrc] at this
    exact this rfl
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR,
      inv_mul_lt_iff₀ hR, mul_one]
    exact (hC x hx).trans_lt (by simp [R]; linarith [le_max_left C 0])
  · simp only [smul_inv_smul₀ hR.ne', ContinuousLinearEquiv.apply_symm_apply]
    exact φ.left_inv (hKs hx)

variable {f : sphere (0 : F) 1 → sphere (0 : F) 1} {a b : sphere (0 : F) 1}

omit [InnerProductSpace ℝ F] in
/-- If `f` maps the connected sphere onto itself and `a ≠ b`, some point lies off `f⁻¹{a, b}`:
otherwise `f⁻¹(a)` would be a nonempty proper clopen set. -/
private theorem exists_notMem_preimage_pair [PreconnectedSpace (sphere (0 : F) 1)]
    (hf : Continuous f) (hfs : Surjective f) (hab : a ≠ b) : ∃ x₀, x₀ ∉ f ⁻¹' {a, b} := by
  by_contra! h
  have hA : IsClopen (f ⁻¹' {a}) := by
    refine ⟨isClosed_singleton.preimage hf, ?_⟩
    rw [show f ⁻¹' {a} = (f ⁻¹' {b})ᶜ by
      ext x
      have hx := h x
      simp only [mem_preimage, mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with hx | hx <;> simp [hx, hab, hab.symm]]
    exact (isClosed_singleton.preimage hf).isOpen_compl
  obtain ⟨xa, hxa⟩ := hfs a
  obtain ⟨xb, hxb⟩ := hfs b
  rcases isClopen_iff.1 hA with h' | h'
  · exact notMem_empty xa (h' ▸ hxa)
  · have : xb ∈ f ⁻¹' {a} := h' ▸ mem_univ xb
    exact hab (this.symm.trans hxb)

/-- **Brown's push off one inverse set.** Let `f` map the sphere onto itself, injectively off
`f⁻¹{a, b}`, and let `Q` be a compact set containing `f⁻¹{a, b}` whose image misses a point
`p ≠ a, b`. Then there is a map `g`, continuous and injective on `Q` off `f⁻¹(a)`, which sends
exactly the points of `f⁻¹(a)` in `Q` to one point `c`. It is the identity on `f⁻¹(b)` and
`f⁻¹ ∘ k ∘ f` elsewhere, for a squeeze `k` which is the identity near `b` and moves `f(Q)` off
`a`. -/
private theorem exists_continuousOn_injOn_sdiff_preimage [FiniteDimensional ℝ F]
    (hf : Continuous f) (hfs : Surjective f) (hab : a ≠ b) (hinj : InjOn f (f ⁻¹' {a, b})ᶜ)
    {Q : Set (sphere (0 : F) 1)} (hQ : IsCompact Q) (hQab : f ⁻¹' {a, b} ⊆ Q)
    {p : sphere (0 : F) 1} (hpQ : p ∉ f '' Q) (hap : a ≠ p) (hbp : b ≠ p) :
    ∃ g : sphere (0 : F) 1 → sphere (0 : F) 1, ∃ c, ContinuousOn g Q ∧
      InjOn g (Q \ f ⁻¹' {a}) ∧ ∀ x ∈ Q, g x = c ↔ f x = a := by
  classical
  have : Nonempty (sphere (0 : F) 1) := ⟨p⟩
  set U : Set (sphere (0 : F) 1) := (f ⁻¹' {a, b})ᶜ
  -- A squeeze `k`, the identity near `b`, carrying `f(Q)` off `a`.
  obtain ⟨k, hkc, hki, hkid, hkN⟩ := exists_continuousOn_injOn_mapsTo_sphere hbp (hQ.image hf)
    hpQ (isOpen_compl_singleton.mem_nhds hab.symm)
  have hkb : k b = b := hkid.eq_of_nhds
  have hfQ {x : sphere (0 : F) 1} (hx : x ∈ Q) : f x ≠ p := fun h ↦ hpQ ⟨x, hx, h⟩
  -- Off `f⁻¹{a, b}`, `f` is inverted by `finv`, continuously.
  set finv := invFunOn f U
  have hfU : f '' U = ({a, b} : Set (sphere (0 : F) 1))ᶜ := by
    ext y
    refine ⟨fun ⟨x, hx, hxy⟩ ↦ hxy ▸ hx, fun hy ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hfs y
    exact ⟨x, hy, rfl⟩
  have hfinv : ContinuousOn finv (f '' U) :=
    hf.continuousOn.continuousOn_invFunOn_image_of_isCompact isCompact_univ (subset_univ U) hinj
      (disjoint_left.2 fun _ ⟨x, hx, hxy⟩ ⟨x', hx', hx'y⟩ ↦ hx' <| by
        have : f x ∈ ({a, b} : Set (sphere (0 : F) 1)) := not_not.1 hx.2
        rw [mem_preimage, hx'y, ← hxy]
        exact this)
  have hfinvU {y : sphere (0 : F) 1} (hy : y ∉ ({a, b} : Set (sphere (0 : F) 1))) :
      finv y ∈ U ∧ f (finv y) = y :=
    ⟨invFunOn_mem (hfU.symm ▸ hy : y ∈ f '' U), invFunOn_eq (hfU.symm ▸ hy : y ∈ f '' U)⟩
  -- `k ∘ f` sends `Q \ f⁻¹(b)` off `{a, b}`.
  have hkf {x : sphere (0 : F) 1} (hx : x ∈ Q) (hxb : f x ≠ b) :
      k (f x) ∉ ({a, b} : Set (sphere (0 : F) 1)) := by
    rintro (h | h)
    · exact hkN (mem_image_of_mem f hx) h
    · exact hxb (hki (hfQ hx) hbp (h.trans hkb.symm))
  -- The map `g`: the identity on `f⁻¹(b)` and `f⁻¹ ∘ k ∘ f` elsewhere.
  set g : sphere (0 : F) 1 → sphere (0 : F) 1 := fun x ↦ if f x = b then x else finv (k (f x))
  have hgb {x : sphere (0 : F) 1} (hx : f x = b) : g x = x := by simp [g, hx]
  have hg {x : sphere (0 : F) 1} (hx : f x ≠ b) : g x = finv (k (f x)) := by simp [g, hx]
  have hfg {x : sphere (0 : F) 1} (hx : x ∈ Q) (hxb : f x ≠ b) :
      g x ∈ U ∧ f (g x) = k (f x) := hg hxb ▸ hfinvU (hkf hx hxb)
  obtain ⟨x₁, hx₁⟩ := hfs a
  have hka : k a ∉ ({a, b} : Set (sphere (0 : F) 1)) := by
    simpa [hx₁] using hkf (x := x₁) (hQab (by simp [hx₁])) (by rw [hx₁]; exact hab)
  have hcU := hfinvU hka
  refine ⟨g, finv (k a), fun x hx ↦ ?_, ?_,
    fun x hx ↦ ⟨fun h ↦ ?_, fun h ↦ by rw [hg (h ▸ hab), h]⟩⟩
  · by_cases hxb : f x = b
    · -- Near `f⁻¹(b)` the squeeze is the identity, so `g` is the identity.
      obtain ⟨W, hWk, hW, hbW⟩ := _root_.eventually_nhds_iff.1 hkid
      have hid : g =ᶠ[𝓝 x] id := by
        filter_upwards [hf.continuousAt.preimage_mem_nhds (by
          rw [hxb]
          exact (hW.inter isOpen_compl_singleton).mem_nhds ⟨hbW, hab.symm⟩)] with x' ⟨hx'W, hx'a⟩
        by_cases hx'b : f x' = b
        · exact hgb hx'b
        · have hx'U : x' ∈ U := by
            simp only [U, mem_compl_iff, mem_preimage, mem_insert_iff, mem_singleton_iff, not_or]
            exact ⟨hx'a, hx'b⟩
          rw [hg hx'b, hWk _ hx'W, id]
          exact hinj.leftInvOn_invFunOn hx'U
      exact (continuousAt_id.congr (hid.symm)).continuousWithinAt
    · -- Elsewhere `g` is `f⁻¹ ∘ k ∘ f`, a composite of maps continuous at the relevant points.
      have hcont : ContinuousWithinAt (fun x ↦ finv (k (f x))) (Q ∩ {x | f x ≠ b}) x :=
        (hfinv _ (hfU.symm ▸ hkf hx hxb)).comp
          ((hkc.continuousAt (isOpen_compl_singleton.mem_nhds (hfQ hx))).comp
            hf.continuousAt).continuousWithinAt
          fun x' hx' ↦ hfU.symm ▸ hkf hx'.1 hx'.2
      exact (hcont.congr (fun x' hx' ↦ hg hx'.2) (hg hxb)).mono_of_mem_nhdsWithin
        (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
          (hf.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hxb))))
  · -- `g` is injective off `f⁻¹(a)`: it fixes `f⁻¹(b)`, maps the rest into `U`, and `k ∘ f`
    -- is injective on `Q \ f⁻¹{a, b}`.
    rintro x ⟨hx, hxa⟩ x' ⟨hx', hx'a⟩ h
    by_cases hxb : f x = b <;> by_cases hx'b : f x' = b
    · rwa [hgb hxb, hgb hx'b] at h
    · have := (hfg hx' hx'b).1
      rw [← h, hgb hxb] at this
      exact absurd (Or.inr hxb) this
    · have := (hfg hx hxb).1
      rw [h, hgb hx'b] at this
      exact absurd (Or.inr hx'b) this
    · have hk : f x = f x' := hki (hfQ hx) (hfQ hx') <| by
        rw [← (hfg hx hxb).2, ← (hfg hx' hx'b).2, h]
      refine hinj ?_ ?_ hk <;> simp_all [U]
  · -- A point sent to `c = f⁻¹(k a)` is not in `f⁻¹(b)`, since `c ∈ U`, so `k (f x) = k a`.
    by_cases hxb : f x = b
    · rw [hgb hxb] at h
      have : f (finv (k a)) ∈ ({a, b} : Set (sphere (0 : F) 1)) := by
        rw [← h, hxb]
        simp
      exact absurd this hcU.1
    · exact hki (hfQ hx) hap (by rw [← (hfg hx hxb).2, h, hcU.2])

/-- **Brown's theorem on two inverse sets.** Let `f` be a continuous surjection of the unit sphere
`Sⁿ` of a real inner product space of dimension `n + 1`, `n ≥ 2`, onto itself, and let `a ≠ b` be
two points such that `f` is injective off `f⁻¹{a, b}`. Then the fibre `f⁻¹(a)` is cellular,
modelled on any real normed space of dimension `n`. -/
theorem isCellularSet_preimage_singleton_of_injOn (hn : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hf : Continuous f) (hfs : Surjective f) (hab : a ≠ b)
    (hinj : InjOn f (f ⁻¹' {a, b})ᶜ) : IsCellularSet E (f ⁻¹' {a}) := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have : PreconnectedSpace (sphere (0 : F) 1) := Subtype.preconnectedSpace
    (isConnected_sphere (by rw [← finrank_eq_rank]; exact_mod_cast (by omega : 1 < finrank ℝ F))
      0 zero_le_one).2
  obtain ⟨x₀, hx₀⟩ := exists_notMem_preimage_pair hf hfs hab
  have hfx₀ : f x₀ ∉ ({a, b} : Set (sphere (0 : F) 1)) := hx₀
  -- A cell `Q = ψ(closedBall)` missing `x₀` and containing both fibres in its interior; its
  -- image misses `f x₀`.
  obtain ⟨ψ, hψc, hψi, hψx₀, hKψ⟩ := exists_continuous_injective_subset_image_ball hEF
    (((finite_singleton b).insert a).isClosed.preimage hf).isCompact hx₀
  have hpQ : f x₀ ∉ f '' (ψ '' closedBall 0 1) := by
    rintro ⟨x, ⟨z, -, rfl⟩, hz⟩
    exact hψx₀ ⟨z, hinj (fun h ↦ hfx₀ (hz ▸ h)) hx₀ hz⟩
  obtain ⟨g, c, hgc, hgi, hga⟩ := exists_continuousOn_injOn_sdiff_preimage hf hfs hab hinj
    ((isCompact_closedBall (0 : E) 1).image hψc) (hKψ.trans (image_mono ball_subset_closedBall))
    hpQ (fun h ↦ hfx₀ (h ▸ by simp)) (fun h ↦ hfx₀ (h ▸ by simp))
  -- Brown's theorem on one inverse set, for `g ∘ ψ` on the closed ball.
  have hψQ : MapsTo ψ (closedBall 0 1) (ψ '' closedBall 0 1) := mapsTo_image ψ _
  have hcell := isCellularSet_closedBall_inter_preimage (E := E) (f := g ∘ ψ) (y := c) hn hEF
    (hgc.comp hψc.continuousOn hψQ)
    (fun z hz z' hz' h ↦ hψi (hgi ⟨hψQ hz.1, fun h' ↦ hz.2 ((hga _ (hψQ hz.1)).2 h')⟩
      ⟨hψQ hz'.1, fun h' ↦ hz'.2 ((hga _ (hψQ hz'.1)).2 h')⟩ h))
    (by
      rintro ⟨z, hz, hzc⟩
      obtain ⟨z', hz', hψz⟩ := hKψ (show ψ z ∈ f ⁻¹' {a, b} by
        simp [(hga _ (hψQ (sphere_subset_closedBall hz))).1 hzc])
      rw [hψi hψz] at hz'
      exact (mem_sphere_zero_iff_norm.1 hz).not_lt (mem_ball_zero_iff.1 hz'))
    (by
      obtain ⟨x, hx⟩ := hfs a
      obtain ⟨z, hz, rfl⟩ := hKψ (show x ∈ f ⁻¹' {a, b} by simp [hx])
      exact ⟨z, ball_subset_closedBall hz, (hga _ (hψQ (ball_subset_closedBall hz))).2 hx⟩)
  -- The fibre of `g ∘ ψ` over `c` is carried by `ψ` onto `f⁻¹(a)`.
  convert hcell.image hψc hψi using 1
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hKψ (show x ∈ f ⁻¹' {a, b} by simp_all)
    exact ⟨z, ⟨ball_subset_closedBall hz, (hga _ (hψQ (ball_subset_closedBall hz))).2 hx⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hzc⟩, rfl⟩
    exact (hga _ (hψQ hz)).1 hzc

end TauCeti
