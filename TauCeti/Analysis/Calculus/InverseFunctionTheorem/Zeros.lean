/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.InverseFunctionTheorem.Family

/-!
# Nondegenerate zeros of converging families

A zero `x₀` of a `C¹` map `Φ₀ : E → F` is *nondegenerate* when the derivative `D Φ₀ (x₀)` is
invertible. Nondegenerate zeros are stable: if `Φ i → Φ₀` in `C¹` along a filter `l`, every map
`Φ i` close enough to the limit has exactly one zero near `x₀`, this zero is again nondegenerate,
and it converges to `x₀`
(`TauCeti.exists_tendsto_inter_preimage_zero_eq_singleton_of_tendstoContDiffAt`). This is the
inverse function theorem for converging families
(`TauCeti.exists_openPartialHomeomorph_tendstoContDiffAt_symm`) applied at the value `0`: the maps
`Φ i` restrict to partial homeomorphisms with one common source around `x₀` whose targets all
contain one neighbourhood of `0`, and their inverses converge.

On a compact set `K` whose zeros of `Φ₀` are all nondegenerate and lie in the interior of `K`,
the zeros are moreover isolated, hence finitely many, and they persist as a whole: eventually along
`l` the zeros of `Φ i` in `K` are in bijection with those of `Φ₀`, through a bijection that moves
every zero of `Φ₀` continuously, and they are all nondegenerate
(`TauCeti.exists_tendsto_bijOn_inter_preimage_zero_of_tendstoContDiffAt`). Away from the zeros of
`Φ₀`, the maps `Φ i` have no zeros in `K` for `i` close to the limit, by compactness of `K` and
continuous convergence of the values. In particular the number of zeros in `K` is eventually
constant (`TauCeti.eventually_ncard_inter_preimage_zero_eq_of_tendstoContDiffAt`). The
hypothesis that the zeros of `Φ₀` lie in the interior of `K` cannot be dropped: zeros of nearby
maps may leave `K` through its boundary.

A typical application is the transverse preimage `u⁻¹(D)` of a codimension-two submanifold
`D = g⁻¹(0)` under a map `u` of a surface, the set of zeros of `g ∘ u`: transverse intersection
points are nondegenerate zeros, so along a `C¹`-converging family of maps their number is locally
constant and they move continuously. This is the count that makes a stabilization of unstable
sphere components by the full preimage of a transverse cut carry a fixed number of extra marked
points over a neighbourhood of a given map.

## Main results

* `TauCeti.exists_tendsto_inter_preimage_zero_eq_singleton_of_tendstoContDiffAt`: a nondegenerate
  zero persists, uniquely near the original zero, and depends continuously on the parameter.
* `TauCeti.exists_tendsto_bijOn_inter_preimage_zero_of_tendstoContDiffAt`: the zeros in a compact
  set persist as a whole.
* `TauCeti.eventually_ncard_inter_preimage_zero_eq_of_tendstoContDiffAt`: the number of zeros in
  a compact set is eventually constant.

## References

* V. Guillemin and A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 1, §6
  (stability of transversality and of finite transverse preimages).
* K. Cieliebak and K. Mohnke, *Symplectic hypersurfaces and transversality in Gromov–Witten
  theory*, J. Symplectic Geom. 5 (2007), 281–356, Section 6 (stabilization of domains by
  transverse preimages of a hypersurface).
-/

public section

open Set Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type*} {l : Filter ι} {Φ : ι → E → F} {Φ₀ : E → F} {s K : Set E}

/-- **Persistence of a nondegenerate zero.** Let `Φ i → Φ₀` in `C¹` at every point of an open set
`s`, with the maps `Φ i` eventually `C¹` on `s`, and let `x₀ ∈ s` be a zero of `Φ₀` at which
`D Φ₀ (x₀)` is invertible. Then there is an open neighbourhood `U ⊆ s` of `x₀` in which `x₀` is the
only zero of `Φ₀`, and points `z i` converging to `x₀` such that eventually along `l` the point
`z i` is the only zero of `Φ i` in `U`, and `D Φ i (z i)` is invertible. -/
theorem exists_tendsto_inter_preimage_zero_eq_singleton_of_tendstoContDiffAt {x₀ : E}
    (hs : IsOpen s) (hx₀ : x₀ ∈ s) (hΦ : ∀ᶠ i in l, ContDiffOn 𝕜 1 (Φ i) s)
    (hΦ₀ : ContDiffOn 𝕜 1 Φ₀ s) (hconv : ∀ x ∈ s, TendstoContDiffAt 𝕜 1 Φ Φ₀ l x)
    (hzero : Φ₀ x₀ = 0) (hinv : (fderiv 𝕜 Φ₀ x₀).IsInvertible) :
    ∃ U, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ s ∧ U ∩ Φ₀ ⁻¹' {0} = {x₀} ∧
      ∃ z : ι → E, Tendsto z l (𝓝 x₀) ∧
        ∀ᶠ i in l, U ∩ Φ i ⁻¹' {0} = {z i} ∧ (fderiv 𝕜 (Φ i) (z i)).IsInvertible := by
  obtain ⟨e₀, e, T, -, hT, he₀, hx₀e, hes, hTe, -, hev, hsymm⟩ :=
    exists_openPartialHomeomorph_tendstoContDiffAt_symm hs hx₀ le_rfl hΦ hΦ₀ hconv hinv
  rw [hzero] at hT
  have hsymm₀ : e₀.symm 0 = x₀ := by rw [← hzero, ← he₀, e₀.left_inv hx₀e]
  refine ⟨e₀.source, e₀.open_source, hx₀e, hes, ?_, fun i ↦ (e i).symm 0, ?_, ?_⟩
  · -- `Φ₀ = e₀` is injective on its source.
    refine eq_singleton_iff_unique_mem.2 ⟨⟨hx₀e, hzero⟩, fun x ⟨hx, hx0⟩ ↦ ?_⟩
    refine e₀.injOn hx hx₀e ?_
    simp only [he₀, mem_preimage, mem_singleton_iff] at hx0 ⊢
    rw [hx0, hzero]
  · -- The inverses converge continuously at `0`.
    have h := (hsymm 0 hT).tendsto.comp (tendsto_id.prodMk (tendsto_const_nhds (x := (0 : F))))
    rwa [hsymm₀] at h
  · filter_upwards [hev, hΦ] with i ⟨hei, hsrc, hT', hsymmc⟩ hΦi
    have h0 : (0 : F) ∈ (e i).target := hT' hT
    have hz : (e i).symm 0 ∈ (e i).source := (e i).map_target h0
    have hzU : (e i).symm 0 ∈ e₀.source := hsrc ▸ hz
    have hΦz : Φ i ((e i).symm 0) = 0 := by rw [← hei, (e i).right_inv h0]
    refine ⟨eq_singleton_iff_unique_mem.2 ⟨⟨hzU, hΦz⟩, fun x ⟨hx, hx0⟩ ↦ ?_⟩, ?_⟩
    · -- `Φ i = e i` is injective on the common source.
      refine (e i).injOn (hsrc ▸ hx) hz ?_
      simp only [hei, mem_preimage, mem_singleton_iff] at hx0 ⊢
      rw [hx0, hΦz]
    · -- The inverse of `e i` is differentiable at `0`, so the derivative at `z i` is invertible.
      have hd : DifferentiableAt 𝕜 (e i) ((e i).symm 0) := by
        rw [hei]
        exact (hΦi.contDiffAt (hs.mem_nhds (hes hzU))).differentiableAt one_ne_zero
      have hds : DifferentiableAt 𝕜 (e i).symm (e i ((e i).symm 0)) := by
        rw [(e i).right_inv h0]
        exact (hsymmc.contDiffAt ((e i).open_target.mem_nhds h0)).differentiableAt one_ne_zero
      simpa only [hei] using (e i).isInvertible_fderiv hz hd hds

omit [CompleteSpace E] in
/-- The zeros of a `C¹` map in a compact set `K`, all nondegenerate, form a finite set. -/
private theorem finite_inter_preimage_zero (hs : IsOpen s) (hK : IsCompact K) (hKs : K ⊆ s)
    (hΦ₀ : ContDiffOn 𝕜 1 Φ₀ s) (hinv : ∀ x ∈ K ∩ Φ₀ ⁻¹' {0}, (fderiv 𝕜 Φ₀ x).IsInvertible) :
    (K ∩ Φ₀ ⁻¹' {0}).Finite := by
  have hclosed : IsClosed (K ∩ Φ₀ ⁻¹' {0}) :=
    (hΦ₀.continuousOn.mono hKs).preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton
  refine (hK.of_isClosed_subset hclosed inter_subset_left).finite_inter_preimage_of_hasFDerivAt
    (fun x hx ↦ ((hΦ₀.contDiffAt (hs.mem_nhds (hKs hx.1))).differentiableAt
      one_ne_zero).hasFDerivAt) fun x hx ↦ ?_
  obtain ⟨L, hL⟩ := hinv x hx
  rw [← hL]
  exact ⟨_, L.antilipschitzWith⟩

omit [CompleteSpace E] in
/-- Away from the zeros of the limit, the members of a converging family have no zeros on a
compact set: if `Φ i → Φ₀` continuously at every point of a compact set `A` on which `Φ₀` does not
vanish, then eventually along `l` the map `Φ i` does not vanish on `A`. -/
private theorem eventually_forall_ne_zero {A : Set E} (hA : IsCompact A)
    (hconv : ∀ a ∈ A, Tendsto (fun p : ι × E ↦ Φ p.1 p.2) (l ×ˢ 𝓝 a) (𝓝 (Φ₀ a)))
    (hne : ∀ a ∈ A, Φ₀ a ≠ 0) : ∀ᶠ i in l, ∀ a ∈ A, Φ i a ≠ 0 := by
  have h := hA.mem_prod_nhdsSet_of_forall (s := {p : ι × E | Φ p.1 p.2 ≠ 0})
    fun a ha ↦ (hconv a ha).eventually (isOpen_ne.mem_nhds (hne a ha))
  exact (Filter.Eventually.curry h).mono fun _ hi ↦ hi.self_of_nhdsSet

/-- **Persistence of the zeros in a compact set.** Let `Φ i → Φ₀` in `C¹` at every point of an
open set `s`, with the maps `Φ i` eventually `C¹` on `s`, and let `K ⊆ s` be compact. Suppose that
every zero of `Φ₀` in `K` lies in the interior of `K` and is nondegenerate. Then there are points
`z i x`, converging to `x` for every zero `x` of `Φ₀` in `K`, such that eventually along `l` the map
`x ↦ z i x` is a bijection from the zeros of `Φ₀` in `K` onto the zeros of `Φ i` in `K`, and every
zero of `Φ i` in `K` is nondegenerate. -/
theorem exists_tendsto_bijOn_inter_preimage_zero_of_tendstoContDiffAt (hs : IsOpen s)
    (hK : IsCompact K) (hKs : K ⊆ s) (hΦ : ∀ᶠ i in l, ContDiffOn 𝕜 1 (Φ i) s)
    (hΦ₀ : ContDiffOn 𝕜 1 Φ₀ s) (hconv : ∀ x ∈ s, TendstoContDiffAt 𝕜 1 Φ Φ₀ l x)
    (hint : K ∩ Φ₀ ⁻¹' {0} ⊆ interior K)
    (hinv : ∀ x ∈ K ∩ Φ₀ ⁻¹' {0}, (fderiv 𝕜 Φ₀ x).IsInvertible) :
    ∃ z : ι → E → E, (∀ x ∈ K ∩ Φ₀ ⁻¹' {0}, Tendsto (fun i ↦ z i x) l (𝓝 x)) ∧
      ∀ᶠ i in l, BijOn (z i) (K ∩ Φ₀ ⁻¹' {0}) (K ∩ Φ i ⁻¹' {0}) ∧
        ∀ x ∈ K ∩ Φ i ⁻¹' {0}, (fderiv 𝕜 (Φ i) x).IsInvertible := by
  set Z := K ∩ Φ₀ ⁻¹' {0}
  have hZfin : Z.Finite := finite_inter_preimage_zero hs hK hKs hΦ₀ hinv
  -- Disjoint open neighbourhoods `V x` of the finitely many zeros of `Φ₀`.
  obtain ⟨V, hV, hVdisj⟩ := hZfin.t2_separation
  -- Around each zero, the zero persists uniquely in a neighbourhood `U x ⊆ V x ∩ interior K`.
  have hloc : ∀ x ∈ Z, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ s ∩ interior K ∩ V x ∧
      ∃ w : ι → E, Tendsto w l (𝓝 x) ∧
        ∀ᶠ i in l, U ∩ Φ i ⁻¹' {0} = {w i} ∧ (fderiv 𝕜 (Φ i) (w i)).IsInvertible := by
    intro x hx
    have hs' : IsOpen (s ∩ interior K ∩ V x) := (hs.inter isOpen_interior).inter (hV x).2
    have hxs' : x ∈ s ∩ interior K ∩ V x := ⟨⟨hKs hx.1, hint hx⟩, (hV x).1⟩
    obtain ⟨U, hU, hxU, hUs, -, w, hw, hev⟩ :=
      exists_tendsto_inter_preimage_zero_eq_singleton_of_tendstoContDiffAt hs' hxs'
        (hΦ.mono fun i hi ↦ hi.mono fun y hy ↦ hy.1.1) (hΦ₀.mono fun y hy ↦ hy.1.1)
        (fun y hy ↦ hconv y hy.1.1) hx.2 (hinv x hx)
    exact ⟨U, hU, hxU, hUs, w, hw, hev⟩
  choose! U hU hxU hUs w hw hev using hloc
  -- Off the neighbourhoods `U x`, the maps `Φ i` eventually have no zeros in `K`.
  have haway : ∀ᶠ i in l, ∀ a ∈ K \ ⋃ x ∈ Z, U x, Φ i a ≠ 0 := by
    refine eventually_forall_ne_zero
      (hK.diff (isOpen_biUnion fun x hx ↦ hU x hx)) (fun a ha ↦ (hconv a (hKs ha.1)).tendsto)
      fun a ha h0 ↦ ha.2 (mem_biUnion ⟨ha.1, h0⟩ (hxU a ⟨ha.1, h0⟩))
  refine ⟨fun i x ↦ w x i, fun x hx ↦ hw x hx, ?_⟩
  filter_upwards [haway, (hZfin.eventually_all (p := fun x i ↦ U x ∩ Φ i ⁻¹' {0} = {w x i} ∧
    (fderiv 𝕜 (Φ i) (w x i)).IsInvertible)).2 hev] with i hi hall
  -- The zero `w x i` of `Φ i` is the only one in `U x`.
  have hmem (x : E) (hx : x ∈ Z) : w x i ∈ U x ∩ Φ i ⁻¹' {0} := by
    rw [(hall x hx).1]
    exact mem_singleton _
  -- Every zero of `Φ i` in `K` lies in some `U x`, hence is some `w x i`.
  have hsurj : ∀ y ∈ K ∩ Φ i ⁻¹' {0}, ∃ x ∈ Z, w x i = y := fun y ⟨hyK, hy0⟩ ↦ by
    by_contra hne
    simp only [not_exists, not_and] at hne
    refine hi y ⟨hyK, fun hyU ↦ ?_⟩ hy0
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyU
    have h : y ∈ U x ∩ Φ i ⁻¹' {0} := ⟨hyx, hy0⟩
    rw [(hall x hx).1] at h
    exact hne x hx h.symm
  refine ⟨⟨fun x hx ↦ ⟨interior_subset (hUs x hx (hmem x hx).1).1.2, (hmem x hx).2⟩,
    fun x hx x' hx' hxx' ↦ ?_, hsurj⟩, fun y hy ↦ ?_⟩
  · -- Distinct zeros of `Φ₀` have disjoint neighbourhoods `V x`.
    by_contra hne
    exact (hVdisj hx hx' hne).ne_of_mem ((hUs x hx (hmem x hx).1).2)
      ((hUs x' hx' (hmem x' hx').1).2) hxx'
  · obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact (hall x hx).2

/-- **The number of zeros in a compact set is eventually constant.** Under the hypotheses of
`TauCeti.exists_tendsto_bijOn_inter_preimage_zero_of_tendstoContDiffAt`, eventually along `l` the
map `Φ i` has as many zeros in `K` as `Φ₀`. -/
theorem eventually_ncard_inter_preimage_zero_eq_of_tendstoContDiffAt (hs : IsOpen s)
    (hK : IsCompact K) (hKs : K ⊆ s) (hΦ : ∀ᶠ i in l, ContDiffOn 𝕜 1 (Φ i) s)
    (hΦ₀ : ContDiffOn 𝕜 1 Φ₀ s) (hconv : ∀ x ∈ s, TendstoContDiffAt 𝕜 1 Φ Φ₀ l x)
    (hint : K ∩ Φ₀ ⁻¹' {0} ⊆ interior K)
    (hinv : ∀ x ∈ K ∩ Φ₀ ⁻¹' {0}, (fderiv 𝕜 Φ₀ x).IsInvertible) :
    ∀ᶠ i in l, (K ∩ Φ i ⁻¹' {0}).ncard = (K ∩ Φ₀ ⁻¹' {0}).ncard := by
  obtain ⟨z, -, hev⟩ :=
    exists_tendsto_bijOn_inter_preimage_zero_of_tendstoContDiffAt hs hK hKs hΦ hΦ₀ hconv hint hinv
  filter_upwards [hev] with i hi
  rw [← hi.1.image_eq, hi.1.injOn.ncard_image]

end TauCeti
