/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Topology.CellularSet.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Separation.Connected
import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.CellularSet.InverseSet.Normed
import TauCeti.Topology.Separation.InvFunOn
import TauCeti.Topology.Sphere.Shrink
import TauCeti.Topology.Sphere.Stereographic

/-!
# Inverse sets of maps into spheres are cellular

Let `Q` be the closed unit ball of a finite-dimensional real normed space `E` of dimension `n`,
and let `f` map `Q` continuously into the unit sphere `Sⁿ` of a real normed space of dimension
`n + 1`. Suppose that the fibre `X = Q ∩ f⁻¹(y)` over some point `y` is nonempty and lies in the
open ball, and that `f` is injective on `Q \ X`: in M. Brown's terminology, `X` is the only
*inverse set* of `f`. Then `X` is cellular in `E`
(`TauCeti.isCellularSet_closedBall_inter_preimage`). This is Theorem 3 of Brown's proof of the
generalized Schoenflies theorem. Brown deduces from it that both inverse sets of a map of `Sⁿ` onto
itself with exactly two inverse sets are cellular (his Theorem 4,
`TauCeti.isCellularSet_preimage_singleton_of_injOn`); with the collapse of cellular sets
(`TauCeti.IsCellularSet.exists_collapse`) this identifies the closures of the complementary domains
of a bicollared sphere with cells (his Theorem 5,
`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`).

Theorem 3 reduces to its version for maps between normed spaces of the same dimension,
`TauCeti.isCellularSet_closedBall_inter_preimage_of_finrank_eq`. The sphere `f(∂Q)` separates `Sⁿ`
by the Jordan–Brouwer theorem (`TauCeti.not_isPreconnected_compl_range_sphere`), while the open ball
is mapped onto a connected set disjoint from it, so `f(Q)` misses some point `p`. Reading
`Sⁿ \ {p}` in a stereographic chart turns `f` into a map of `Q` into `ℝⁿ` with the same only
inverse set.

For Theorem 4, let `g` map `Sⁿ` onto itself, injective off the fibres `A = g⁻¹(p)` and
`B = g⁻¹(q)`, `p ≠ q`. Choose `w` with `g w ∉ {p, q}`; a large closed ball `Q` in the stereographic
chart from `w` is a cell containing `B` in its interior. The point `g w` is not in `g(Q)`, so a
radial squeeze about `p` in the stereographic chart from `g w`
(`TauCeti.exists_continuousOn_injOn_mapsTo_sphere`) gives a map `k`, continuous and injective off
`g w`, which is the identity near `p` and pushes `g(Q)` off `q`. On `Q`, the map `g⁻¹ ∘ k ∘ g`,
extended by the identity near `A`, collapses `B` to the point `g⁻¹(k q)` and is injective
elsewhere. So `B` is the only inverse set of a map of the cell `Q` into `Sⁿ`, and Theorem 3
applies. The fibre `A` is cellular by exchanging `p` and `q`.

## Main results

* `TauCeti.isCellularSet_closedBall_inter_preimage`: **Brown's theorem on inverse sets**: the only
  inverse set of a map of an `n`-cell into `Sⁿ` is cellular.
* `TauCeti.isCellularSet_preimage_singleton_of_injOn`: **Brown's theorem on two inverse sets**:
  if a map of `Sⁿ`, `n ≥ 2`, onto itself is injective off its fibres over `p ≠ q`, its fibre over
  `q` is cellular (and, exchanging `p` and `q`, so is its fibre over `p`).

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorems 0, 3 and 4.
-/

public section

open Function Metric Module Set Filter Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section OneInverseSet

variable [NormedSpace ℝ F] {f : E → sphere (0 : F) 1} {y : sphere (0 : F) 1}

omit [NormedSpace ℝ F] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Two points of the closed ball with the same image under `f`, not in the fibre over `y`, are
equal, when `f` is injective off that fibre. -/
private theorem eq_of_apply_eq (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {y})) {x x' : E}
    (hx : x ∈ closedBall 0 1) (hx' : x' ∈ closedBall 0 1) (h : f x = f x') (hy : f x ≠ y) :
    x = x' :=
  hinj ⟨hx, hy⟩ ⟨hx', fun h' ↦ hy (h.trans h')⟩ h

omit [FiniteDimensional ℝ E] in
/-- **The image of the closed ball is not the whole sphere.** By the Jordan–Brouwer separation
theorem the embedded sphere `f(∂Q)` separates `Sⁿ`, while `f` maps the open ball onto a connected
set disjoint from `f(∂Q)`. -/
private theorem exists_notMem_image_closedBall (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hf : ContinuousOn f (closedBall 0 1)) (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {y}))
    (hy : y ∉ f '' sphere 0 1) : ∃ p, p ∉ f '' closedBall 0 1 := by
  by_contra! h
  have hne {x : E} (hx : x ∈ sphere (0 : E) 1) : f x ≠ y := fun h ↦ hy ⟨x, hx, h⟩
  have hc : Continuous fun x : sphere (0 : E) 1 ↦ f x :=
    hf.comp_continuous continuous_subtype_val fun x ↦ sphere_subset_closedBall x.2
  have hi : Injective fun x : sphere (0 : E) 1 ↦ f x := fun x x' h ↦ Subtype.ext <|
    eq_of_apply_eq hinj (sphere_subset_closedBall x.2) (sphere_subset_closedBall x'.2) h (hne x.2)
  -- The complement of `f(∂Q)` is the image of the open ball, which is connected.
  have hrange : (range fun x : sphere (0 : E) 1 ↦ f x)ᶜ = f '' ball 0 1 := by
    ext z
    refine ⟨fun hz ↦ ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := h z
      refine ⟨x, ?_, rfl⟩
      rw [← closedBall_sdiff_sphere]
      exact ⟨hx, fun hxs ↦ hz ⟨⟨x, hxs⟩, rfl⟩⟩
    · rintro ⟨x, hx, rfl⟩ ⟨s, hs⟩
      exact sphere_disjoint_ball.ne_of_mem s.2 hx <| eq_of_apply_eq hinj
        (sphere_subset_closedBall s.2) (ball_subset_closedBall hx) hs (hne s.2)
  exact not_isPreconnected_compl_range_sphere hEF hc hi
    (hrange ▸ isPreconnected_ball.image f (hf.mono ball_subset_closedBall))

/-- **Brown's theorem on inverse sets.** Let `E` be a finite-dimensional real normed space of
dimension `n`, and let `f` map the closed unit ball `Q` of `E` continuously into the unit sphere
`Sⁿ` of a real normed space of dimension `n + 1`. Suppose that the fibre `Q ∩ f⁻¹(y)` of a point
`y` of `f(Q)` lies in the open ball and that `f` is injective off it, so that it is the only
inverse set of `f`. Then this fibre is cellular. -/
theorem isCellularSet_closedBall_inter_preimage (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hf : ContinuousOn f (closedBall 0 1)) (hinj : InjOn f (closedBall 0 1 \ f ⁻¹' {y}))
    (hy : y ∉ f '' sphere 0 1) (hy' : y ∈ f '' closedBall 0 1) :
    IsCellularSet E (closedBall (0 : E) 1 ∩ f ⁻¹' {y}) := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  set n := finrank ℝ E
  obtain ⟨p, hp⟩ := exists_notMem_image_closedBall hEF hf hinj hy
  have hQp {x : E} (hx : x ∈ closedBall 0 1) : f x ≠ p := fun h ↦ hp ⟨x, hx, h⟩
  have hyp : y ≠ p := by
    obtain ⟨x, hx, rfl⟩ := hy'
    exact hQp hx
  -- Read `Sⁿ \ {p}` in a stereographic chart `φ` of the Euclidean sphere.
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  set e := sphereHomeomorphOfFinrankEq (E := F) (F := EuclideanSpace ℝ (Fin (n + 1)))
    (by simp [hEF, n])
  set φ := stereographic' n (e p)
  have hsrc {z : sphere (0 : F) 1} (hz : z ≠ p) : e z ∈ φ.source := by
    rw [stereographic'_source]
    exact e.injective.ne hz
  set f' : E → EuclideanSpace ℝ (Fin n) := fun x ↦ φ (e (f x))
  have hf'y {x : E} (hx : x ∈ closedBall 0 1) : f' x = φ (e y) ↔ f x = y :=
    ⟨fun h ↦ e.injective (φ.injOn (hsrc (hQp hx)) (hsrc hyp) h), fun h ↦ by simp only [f', h]⟩
  have hfib : closedBall 0 1 ∩ f' ⁻¹' {φ (e y)} = closedBall 0 1 ∩ f ⁻¹' {y} := by
    ext x
    exact and_congr_right fun hx ↦ hf'y hx
  rw [← hfib]
  refine isCellularSet_closedBall_inter_preimage_of_finrank_eq (by simp [n])
    (φ.continuousOn.comp (e.continuous.comp_continuousOn hf) fun x hx ↦ hsrc (hQp hx))
    (fun x hx x' hx' h ↦ hinj ⟨hx.1, fun h' ↦ hx.2 ((hf'y hx.1).2 h')⟩
      ⟨hx'.1, fun h' ↦ hx'.2 ((hf'y hx'.1).2 h')⟩
      (e.injective (φ.injOn (hsrc (hQp hx.1)) (hsrc (hQp hx'.1)) h))) ?_ ?_
  · rw [hfib]
    intro x hx
    rw [← closedBall_sdiff_sphere]
    exact ⟨hx.1, fun h ↦ hy ⟨x, h, hx.2⟩⟩
  · obtain ⟨x, hx, rfl⟩ := hy'
    exact ⟨x, hx, rfl⟩

end OneInverseSet

section TwoInverseSets

variable [InnerProductSpace ℝ F] {g : sphere (0 : F) 1 → sphere (0 : F) 1} {p q : sphere (0 : F) 1}

/-- **Trading one inverse set for a point.** Let `g` be a continuous surjection of the unit sphere
onto itself, injective off the fibres `A = g⁻¹(p)` and `B = g⁻¹(q)` over two points `p ≠ q`. Let
`Q` be a compact set containing `B` and missing a point `w` with `g w ∉ {p, q}`. Then there is a
map `φ` of the sphere, continuous on `Q`, whose fibre over some point `w'` within `Q` is exactly `B`
and which is injective on `Q \ B`. It is `g⁻¹ ∘ k ∘ g` for a map `k`, continuous and injective off
`g w`, which is the identity near `p` and pushes `g(Q)` off `q`; near `A` it is the identity. -/
private theorem exists_continuousOn_injOn_preimage_singleton [FiniteDimensional ℝ F]
    (hg : Continuous g) (hgs : Surjective g) (hpq : p ≠ q) (hinj : InjOn g (g ⁻¹' {p, q})ᶜ)
    {Q : Set (sphere (0 : F) 1)} (hQ : IsCompact Q) (hBQ : g ⁻¹' {q} ⊆ Q)
    {w : sphere (0 : F) 1} (hw : g w ∉ ({p, q} : Set (sphere (0 : F) 1))) (hwQ : w ∉ Q) :
    ∃ φ : sphere (0 : F) 1 → sphere (0 : F) 1, ∃ w', ContinuousOn φ Q ∧
      InjOn φ (Q \ g ⁻¹' {q}) ∧ ∀ x ∈ Q, φ x = w' ↔ g x = q := by
  classical
  have : Nonempty (sphere (0 : F) 1) := ⟨p⟩
  set P := (g ⁻¹' {p, q})ᶜ
  have hP {x : sphere (0 : F) 1} : x ∈ P ↔ g x ∉ ({p, q} : Set (sphere (0 : F) 1)) := Iff.rfl
  have hps : p ≠ g w := fun h ↦ hw (h ▸ .inl rfl)
  -- `g(Q)` misses `g w`, since `g` is injective at `w`.
  have hgQ {x : sphere (0 : F) 1} (hx : x ∈ Q) : g x ≠ g w := fun h ↦
    hwQ (hinj (hP.2 (h ▸ hw)) (hP.2 hw) h ▸ hx)
  obtain ⟨k, hkc, hki, hkid, hkN⟩ := exists_continuousOn_injOn_mapsTo_sphere hps
    (hQ.image hg) (fun ⟨x, hx, h⟩ ↦ hgQ hx h) (isOpen_compl_singleton.mem_nhds hpq)
  have hkp : k p = p := hkid.eq_of_nhds
  -- An open neighbourhood `W` of `p`, missing `q`, on which `k` is the identity.
  obtain ⟨W, hWk, hW, hpW⟩ := _root_.eventually_nhds_iff.1
    (hkid.and (isOpen_compl_singleton.mem_nhds hpq))
  -- Off `A`, `k ∘ g` avoids `p` and `q` on `Q`.
  have hkpq {x : sphere (0 : F) 1} (hx : x ∈ Q) (hxp : g x ≠ p) :
      k (g x) ∉ ({p, q} : Set (sphere (0 : F) 1)) := by
    rintro (h | h)
    · exact hxp (hki (hgQ hx) hps (h.trans hkp.symm))
    · exact hkN (mem_image_of_mem g hx) h
  -- The inverse of `g` off the two fibres.
  set ginv := invFunOn g P
  have hginv {y : sphere (0 : F) 1} (hy : y ∉ ({p, q} : Set (sphere (0 : F) 1))) :
      ginv y ∈ P ∧ g (ginv y) = y := by
    obtain ⟨x, rfl⟩ := hgs y
    exact ⟨invFunOn_mem ⟨x, hy, rfl⟩, invFunOn_eq ⟨x, hy, rfl⟩⟩
  set φ : sphere (0 : F) 1 → sphere (0 : F) 1 := fun x ↦ if g x ∈ W then x else ginv (k (g x))
  have hgφ {x : sphere (0 : F) 1} (hx : x ∈ Q) : g (φ x) = k (g x) := by
    by_cases hxW : g x ∈ W
    · simp only [φ, hxW, ite_true, (hWk _ hxW).1, id]
    · simp only [φ, hxW, ite_false, (hginv (hkpq hx fun h ↦ hxW (h ▸ hpW))).2]
  -- Off `A`, `φ` is `g⁻¹ ∘ k ∘ g`.
  have hφ {x : sphere (0 : F) 1} (hxp : g x ≠ p) : φ x = ginv (k (g x)) := by
    by_cases hxW : g x ∈ W
    · have hxP : x ∈ P := by
        rintro (h | h)
        exacts [hxp h, (hWk _ hxW).2 h]
      simp only [φ, hxW, ite_true, (hWk _ hxW).1, id]
      exact (hinj.leftInvOn_invFunOn hxP).symm
    · simp only [φ, hxW, ite_false]
  obtain ⟨b, hb⟩ := hgs q
  have hbQ : b ∈ Q := hBQ hb
  have hqs : q ≠ g w := hb ▸ hgQ hbQ
  have hqp : k q ∉ ({p, q} : Set (sphere (0 : F) 1)) := hb ▸ hkpq hbQ (hb ▸ hpq.symm)
  refine ⟨φ, ginv (k q), fun x hx ↦ ?_, fun x hx x' hx' h ↦ ?_,
    fun x hx ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · by_cases hxp : g x = p
    · -- Near `A`, `φ` is the identity.
      have hid : φ =ᶠ[𝓝 x] id := by
        filter_upwards [hg.continuousAt.preimage_mem_nhds (hW.mem_nhds (hxp ▸ hpW))] with x' hx'
        simp only [φ, mem_preimage.1 hx', ite_true, id]
      exact (continuousAt_id.congr hid.symm).continuousWithinAt
    · -- Elsewhere it is `g⁻¹ ∘ k ∘ g`, and `g⁻¹` is continuous since the sphere is compact.
      have hinv : ContinuousOn ginv (g '' P) :=
        hg.continuousOn.continuousOn_invFunOn_image_of_isCompact isCompact_univ (subset_univ P)
          hinj (disjoint_left.2 fun _ ⟨y, hy, hyz⟩ ⟨y', hy', hy'z⟩ ↦
            hy' (by rw [mem_preimage, hy'z, ← hyz]; exact not_not.1 hy.2))
      have hO : g ⁻¹' {p}ᶜ ∈ 𝓝 x :=
        hg.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hxp)
      have hkg : ContinuousAt (fun x ↦ k (g x)) x :=
        (hkc.continuousAt (isOpen_compl_singleton.mem_nhds (hgQ hx))).comp hg.continuousAt
      have hmaps : MapsTo (fun x ↦ k (g x)) (Q ∩ g ⁻¹' {p}ᶜ) (g '' P) := fun x' hx' ↦
        ⟨_, (hginv (hkpq hx'.1 hx'.2)).1, (hginv (hkpq hx'.1 hx'.2)).2⟩
      have hΦ : ContinuousWithinAt (fun x ↦ ginv (k (g x))) (Q ∩ g ⁻¹' {p}ᶜ) x :=
        ContinuousWithinAt.comp (f := fun x ↦ k (g x)) (hinv _ (hmaps ⟨hx, hxp⟩))
          hkg.continuousWithinAt hmaps
      have hφΦ : φ =ᶠ[𝓝 x] fun x ↦ ginv (k (g x)) := by
        filter_upwards [hO] with x' hx' using hφ hx'
      exact (hΦ.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds hO))).congr_of_eventuallyEq
        (nhdsWithin_le_nhds hφΦ) (hφ hxp)
  · have hgx : g x = g x' := hki (hgQ hx.1) (hgQ hx'.1) (by rw [← hgφ hx.1, ← hgφ hx'.1, h])
    by_cases hxp : g x = p
    · have hxW : g x ∈ W := hxp ▸ hpW
      have hx'W : g x' ∈ W := hgx ▸ hxW
      simpa only [φ, hxW, hx'W, ite_true] using h
    · refine hinj (hP.2 ?_) (hP.2 ?_) hgx
      · rintro (h' | h')
        exacts [hxp h', hx.2 h']
      · rintro (h' | h')
        exacts [hxp (hgx.trans h'), hx'.2 h']
  · have h' := hgφ hx
    rw [h, (hginv hqp).2] at h'
    exact (hki hqs (hgQ hx) h').symm
  · rw [hφ (h ▸ hpq.symm), h]

/-- **Brown's theorem on two inverse sets.** Let `E` be a real normed space of dimension `n ≥ 2`,
and let `g` be a continuous surjection of the unit sphere `Sⁿ` of a real inner product space of
dimension `n + 1` onto itself. Suppose that `g` is injective off the fibres over two points
`p ≠ q`, so that these are its only inverse sets. Then the fibre over `q` is cellular; exchanging
`p` and `q`, so is the fibre over `p`. -/
theorem isCellularSet_preimage_singleton_of_injOn (hn : 2 ≤ finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hg : Continuous g) (hgs : Surjective g) (hpq : p ≠ q)
    (hinj : InjOn g (g ⁻¹' {p, q})ᶜ) : IsCellularSet E (g ⁻¹' {q}) := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  set B := g ⁻¹' {q}
  have hBc : IsCompact B := (isClosed_singleton.preimage hg).isCompact
  -- A point `w` whose image is neither `p` nor `q`: the sphere is infinite.
  obtain ⟨z, hz⟩ : ∃ z : sphere (0 : F) 1, z ∉ ({p, q} : Set (sphere (0 : F) 1)) := by
    have hF : 1 < Module.rank ℝ F := by
      rw [← finrank_eq_rank]
      exact_mod_cast (by omega : 1 < finrank ℝ F)
    have : Infinite (sphere (0 : F) 1) := Set.Infinite.to_subtype <|
      IsPreconnected.infinite_of_nontrivial (isPreconnected_sphere hF 0 1)
        ⟨p, p.2, q, q.2, Subtype.coe_injective.ne hpq⟩
    exact (Set.toFinite _).infinite_compl.nonempty
  obtain ⟨w, rfl⟩ := hgs z
  -- The cell `Q`: a large closed ball in the stereographic chart from `w`, read on `E`. It
  -- contains `B` in its interior, and `w` is not in it.
  obtain ⟨ψ, hψc, hψi, hψw, hBψ⟩ := exists_continuous_injective_subset_image_ball hEF hBc
    fun h ↦ hz (.inr h)
  set Q := ψ '' closedBall 0 1
  have hψQ : MapsTo ψ (closedBall 0 1) Q := mapsTo_image ψ _
  obtain ⟨φ, w', hφc, hφi, hφw⟩ := exists_continuousOn_injOn_preimage_singleton hg hgs hpq hinj
    ((isCompact_closedBall 0 1).image hψc) (hBψ.trans (image_mono ball_subset_closedBall)) hz
    fun ⟨v, _, hv⟩ ↦ hψw v hv
  have hfib {v : E} (hv : v ∈ closedBall 0 1) : φ (ψ v) = w' ↔ ψ v ∈ B := hφw _ (hψQ hv)
  -- `φ ∘ ψ` maps the closed ball into the sphere with the only inverse set `ψ⁻¹(B)`.
  have hX := isCellularSet_closedBall_inter_preimage (f := fun v ↦ φ (ψ v)) (y := w') hEF
    (hφc.comp hψc.continuousOn hψQ)
    (fun v hv v' hv' h ↦ hψi (hφi ⟨hψQ hv.1, fun h' ↦ hv.2 ((hfib hv.1).2 h')⟩
      ⟨hψQ hv'.1, fun h' ↦ hv'.2 ((hfib hv'.1).2 h')⟩ h))
    (fun ⟨v, hv, hvw⟩ ↦ by
      obtain ⟨u, hu, huv⟩ := hBψ ((hfib (sphere_subset_closedBall hv)).1 hvw)
      rw [hψi huv] at hu
      exact (mem_ball_zero_iff.1 hu).ne (mem_sphere_zero_iff_norm.1 hv))
    (by
      obtain ⟨b, hb⟩ := hgs q
      obtain ⟨v, hv, rfl⟩ := hBψ hb
      exact ⟨v, ball_subset_closedBall hv, (hfib (ball_subset_closedBall hv)).2 hb⟩)
  have himg : ψ '' (closedBall 0 1 ∩ (fun v ↦ φ (ψ v)) ⁻¹' {w'}) = B := by
    refine Subset.antisymm ?_ fun x hx ↦ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact (hfib hv.1).1 hv.2
    · obtain ⟨v, hv, rfl⟩ := hBψ hx
      exact ⟨v, ⟨ball_subset_closedBall hv, (hfib (ball_subset_closedBall hv)).2 hx⟩, rfl⟩
  exact himg ▸ hX.image isOpen_univ (subset_univ _) hψc.continuousOn hψi.injOn

end TwoInverseSets

end TauCeti
