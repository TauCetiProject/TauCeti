/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Topology.CellularSet.Basic
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Topology.CellularSet.InverseSet
import TauCeti.Topology.Connected.Basic
import TauCeti.Topology.Separation.InvFunOn
import TauCeti.Topology.Sphere.Shrink

/-!
# The two inverse sets of a map of a sphere onto itself are cellular

Let `f` be a continuous surjection of the unit sphere `Sⁿ` of a real inner product space of
dimension `n + 1 ≥ 3` onto itself, and let `a ≠ b` be two points such that `f` is injective off
`f⁻¹{a, b}`. Then `f⁻¹(a)` is cellular (`TauCeti.isCellularSet_preimage_singleton_of_injOn`),
and so is `f⁻¹(b)`, by exchanging `a` and `b`. This is Theorem 4 of M. Brown's proof of the
generalized Schoenflies theorem, where `f⁻¹(a)` and `f⁻¹(b)` are the only two inverse sets of `f`.
The statement does not ask the fibres to have more than one point.

The proof reduces to Brown's theorem on the only inverse set of a map of a cell into `Sⁿ`
(`TauCeti.isCellularSet_closedBall_inter_preimage`). Choose a point `x₀` off `f⁻¹{a, b}`; it
exists because `Sⁿ` is connected (`TauCeti.exists_notMem_preimage_pair`). In the stereographic
chart from `x₀`, a large closed ball `Q` contains `f⁻¹{a, b}` in its interior
(`TauCeti.exists_continuous_injective_subset_image_ball`), and `p = f x₀` is not in `f(Q)`. A
squeeze `k` of the sphere which is the identity near `b`, continuous and injective off `p`, carries
`f(Q)` off `a` (`TauCeti.exists_continuousOn_injOn_mapsTo_sphere`). The map `g` of `Q` which is
the identity on `f⁻¹(b)` and `f⁻¹ ∘ k ∘ f` elsewhere is then well defined and continuous, since `f`
restricts to a homeomorphism off `f⁻¹{a, b}` (`ContinuousOn.exists_continuousOn_injOn_lift`), and
its only inverse set is `f⁻¹(a)`, which it sends to the single point `f⁻¹(k a)`.

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

variable {f : sphere (0 : F) 1 → sphere (0 : F) 1} {a b : sphere (0 : F) 1}

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
  have : Nonempty (sphere (0 : F) 1) := ⟨p⟩
  set U : Set (sphere (0 : F) 1) := (f ⁻¹' {a, b})ᶜ
  -- A squeeze `k`, the identity near `b`, carrying `f(Q)` off `a`.
  obtain ⟨k, hkc, hki, hkid, hkN⟩ := exists_continuousOn_injOn_mapsTo_sphere hbp (hQ.image hf)
    hpQ (isOpen_compl_singleton.mem_nhds hab.symm)
  have hkb : k b = b := hkid.eq_of_nhds
  have hfQ {x : sphere (0 : F) 1} (hx : x ∈ Q) : f x ≠ p := fun h ↦ hpQ ⟨x, hx, h⟩
  -- Off `f⁻¹{a, b}`, `f` is inverted by `invFunOn f U`, continuously.
  have hfU : f '' U = ({a, b} : Set (sphere (0 : F) 1))ᶜ := by
    ext y
    refine ⟨fun ⟨x, hx, hxy⟩ ↦ hxy ▸ hx, fun hy ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hfs y
    exact ⟨x, hy, rfl⟩
  have hfinv : ContinuousOn (invFunOn f U) (f '' U) :=
    hf.continuousOn.continuousOn_invFunOn_image_of_isCompact isCompact_univ (subset_univ U) hinj
      (disjoint_left.2 fun _ ⟨x, hx, hxy⟩ ⟨x', hx', hx'y⟩ ↦ hx' <| by
        have : f x ∈ ({a, b} : Set (sphere (0 : F) 1)) := not_not.1 hx.2
        rw [mem_preimage, hx'y, ← hxy]
        exact this)
  -- `k ∘ f` sends `Q \ f⁻¹(b)` off `{a, b}`.
  have hkf {x : sphere (0 : F) 1} (hx : x ∈ Q) (hxb : f x ≠ b) :
      k (f x) ∉ ({a, b} : Set (sphere (0 : F) 1)) := by
    rintro (h | h)
    · exact hkN (mem_image_of_mem f hx) h
    · exact hxb (hki (hfQ hx) hbp (h.trans hkb.symm))
  -- The map `g`: the identity on `f⁻¹(b)` and `f⁻¹ ∘ k ∘ f` elsewhere. It is injective off
  -- `f⁻¹(a)`, since `f` is injective off `f⁻¹{a, b}`.
  obtain ⟨g, hgc, hgi, hfg, hgb, hgU⟩ := hf.continuousOn.exists_continuousOn_injOn_lift hfinv hinj
    (fun x _ _ hx ↦ (hfU ▸ hx :))
    (fun x hx ↦ hkc.continuousAt (isOpen_compl_singleton.mem_nhds (hfQ hx)))
    (hki.mono fun _ ⟨x, hx, hxz⟩ ↦ hxz ▸ hfQ hx) hkid (fun x hx hxb ↦ hfU ▸ hkf hx hxb)
    (R := Q \ f ⁻¹' {a}) sdiff_subset (hinj.mono fun x ⟨⟨_, hxa⟩, hxb⟩ ↦ by
      simp only [U, mem_compl_iff, mem_preimage, mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hxa, hxb⟩)
  -- `g` sends exactly the points of `f⁻¹(a)` in `Q` to `c = g x₁`, for any `x₁ ∈ f⁻¹(a)`.
  obtain ⟨x₁, hx₁⟩ := hfs a
  have hx₁Q : x₁ ∈ Q := hQab (by simp [hx₁])
  have hx₁b : f x₁ ≠ b := hx₁ ▸ hab
  refine ⟨g, g x₁, hgc, hgi, fun x hx ↦ ⟨fun h ↦ ?_, fun h ↦ hinj (hgU x hx (h ▸ hab))
    (hgU x₁ hx₁Q hx₁b) (by rw [hfg x hx, hfg x₁ hx₁Q, h, hx₁])⟩⟩
  by_cases hxb : f x = b
  · -- `g x₁` lies in `U`, so it is not the point `x` of `f⁻¹(b)` fixed by `g`.
    refine absurd (hgU x₁ hx₁Q hx₁b) ?_
    rw [← h, hgb x hx hxb]
    simp [U, hxb]
  · exact hki (hfQ hx) hap (by rw [← hfg x hx, h, hfg x₁ hx₁Q, hx₁])

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
  · obtain ⟨z, hz, rfl⟩ := hKψ (show x ∈ f ⁻¹' {a, b} from Or.inl hx)
    exact ⟨z, ⟨ball_subset_closedBall hz, (hga _ (hψQ (ball_subset_closedBall hz))).2 hx⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hzc⟩, rfl⟩
    exact (hga _ (hψQ hz)).1 hzc

end TauCeti
