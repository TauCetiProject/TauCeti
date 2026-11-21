/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.InverseFunctionTheorem.Family
public import TauCeti.Topology.Compactness.Compact

/-!
# Nondegenerate solutions along converging families

A solution `x₀` of `Φ₀ x = y` for a `C¹` map `Φ₀ : E → F` is *nondegenerate* when the derivative
`D Φ₀ (x₀)` is invertible; the main case is a nondegenerate zero, `y = 0`. Nondegenerate solutions
are stable: if `Φ i → Φ₀` in `C¹` along a filter `l`, every map `Φ i` close enough to the limit
has exactly one solution of `Φ i x = y` near `x₀`, this solution is again nondegenerate, and it
converges to `x₀` along `l`
(`TauCeti.exists_tendsto_inter_preimage_singleton_eq_singleton_of_tendstoContDiffAt`). This is the
inverse function theorem for converging families
(`TauCeti.exists_openPartialHomeomorph_tendstoContDiffAt_symm`) applied at the value `y`: the maps
`Φ i` restrict to partial homeomorphisms with one common source around `x₀` whose targets all
contain one neighbourhood of `y`, and their inverses converge.

On a compact set `K` whose solutions of `Φ₀ x = y` are all nondegenerate and lie in the interior of
`K`, these solutions are moreover isolated, hence finitely many
(`IsCompact.finite_inter_preimage_of_differentiableAt_of_isInvertible`), and they persist as a
whole: eventually along `l` the solutions of `Φ i x = y` in `K` are in bijection with those of
`Φ₀ x = y`, through a bijection under which each perturbed solution converges along `l` to the
solution of `Φ₀ x = y` it comes from, and they are all nondegenerate
(`TauCeti.exists_tendsto_bijOn_inter_preimage_singleton_of_tendstoContDiffAt`). Away from the
solutions for `Φ₀`, the maps `Φ i` do not take the value `y` on `K` for `i` close to the limit, by
compactness of `K` and continuous convergence of the values
(`IsCompact.eventually_forall_mem_of_tendsto_prod_nhds`). In particular the number of solutions in
`K` is eventually constant
(`TauCeti.eventually_ncard_inter_preimage_singleton_eq_of_tendstoContDiffAt`). The hypothesis that
the solutions for `Φ₀` lie in the interior of `K` cannot be dropped: solutions for nearby maps may
leave `K` through its boundary.

A typical application is local, to the transverse preimage `u⁻¹(D)` of a codimension-two
submanifold `D` under a map `u` of a surface. In a chart where `D = g⁻¹(0)`, the points of `u⁻¹(D)`
are the zeros of `g ∘ u`, and transverse intersection points are nondegenerate zeros. So in a
compact set of the chart whose zeros are interior, along a `C¹`-converging family of maps the
number of these points is eventually constant and they converge to the original intersection
points. This local count is one ingredient of a stabilization of unstable sphere components by the
full preimage of a transverse cut; the results here are stated only for maps between Banach spaces
on a single compact set.

## Main results

* `TauCeti.exists_tendsto_inter_preimage_singleton_eq_singleton_of_tendstoContDiffAt`: a
  nondegenerate solution persists, uniquely near the original solution, and converges to it
  along `l`.
* `TauCeti.exists_tendsto_bijOn_inter_preimage_singleton_of_tendstoContDiffAt`: the solutions in a
  compact set persist as a whole.
* `TauCeti.eventually_ncard_inter_preimage_singleton_eq_of_tendstoContDiffAt`: the number of
  solutions in a compact set is eventually constant.

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
  {ι : Type*} {l : Filter ι} {Φ : ι → E → F} {Φ₀ : E → F} {s K : Set E} {y : F}

/-- **Persistence of a nondegenerate solution.** Let `Φ i → Φ₀` in `C¹` at every point of an open
set `s`, with the maps `Φ i` eventually `C¹` on `s`, and let `x₀ ∈ s` be a solution of
`Φ₀ x₀ = y` at which `D Φ₀ (x₀)` is invertible. Then there is an open neighbourhood `U ⊆ s` of `x₀`
in which `x₀` is the only solution of `Φ₀ x = y`, and points `z i` converging to `x₀` along `l`
such that eventually along `l` the point `z i` is the only solution of `Φ i x = y` in `U`, and
`D Φ i (z i)` is invertible. -/
theorem exists_tendsto_inter_preimage_singleton_eq_singleton_of_tendstoContDiffAt {x₀ : E}
    (hs : IsOpen s) (hx₀ : x₀ ∈ s) (hΦ : ∀ᶠ i in l, ContDiffOn 𝕜 1 (Φ i) s)
    (hΦ₀ : ContDiffOn 𝕜 1 Φ₀ s) (hconv : ∀ x ∈ s, TendstoContDiffAt 𝕜 1 Φ Φ₀ l x)
    (hy : Φ₀ x₀ = y) (hinv : (fderiv 𝕜 Φ₀ x₀).IsInvertible) :
    ∃ U, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ s ∧ U ∩ Φ₀ ⁻¹' {y} = {x₀} ∧
      ∃ z : ι → E, Tendsto z l (𝓝 x₀) ∧
        ∀ᶠ i in l, U ∩ Φ i ⁻¹' {y} = {z i} ∧ (fderiv 𝕜 (Φ i) (z i)).IsInvertible := by
  obtain ⟨e₀, e, T, -, hT, he₀, hx₀e, hes, hTe, -, hev, hsymm⟩ :=
    exists_openPartialHomeomorph_tendstoContDiffAt_symm hs hx₀ le_rfl hΦ hΦ₀ hconv hinv
  rw [hy] at hT
  have hsymm₀ : e₀.symm y = x₀ := by rw [← hy, ← he₀, e₀.left_inv hx₀e]
  refine ⟨e₀.source, e₀.open_source, hx₀e, hes, ?_, fun i ↦ (e i).symm y, ?_, ?_⟩
  · -- `Φ₀ = e₀` is injective on its source.
    refine eq_singleton_iff_unique_mem.2 ⟨⟨hx₀e, hy⟩, fun x ⟨hx, hxy⟩ ↦ ?_⟩
    refine e₀.injOn hx hx₀e ?_
    simp only [he₀, mem_preimage, mem_singleton_iff] at hxy ⊢
    rw [hxy, hy]
  · -- The inverses converge continuously at `y`.
    have h := (hsymm y hT).tendsto.comp (tendsto_id.prodMk (tendsto_const_nhds (x := y)))
    rwa [hsymm₀] at h
  · filter_upwards [hev, hΦ] with i ⟨hei, hsrc, hT', hsymmc⟩ hΦi
    have hyT : y ∈ (e i).target := hT' hT
    have hz : (e i).symm y ∈ (e i).source := (e i).map_target hyT
    have hzU : (e i).symm y ∈ e₀.source := hsrc ▸ hz
    have hΦz : Φ i ((e i).symm y) = y := by rw [← hei, (e i).right_inv hyT]
    refine ⟨eq_singleton_iff_unique_mem.2 ⟨⟨hzU, hΦz⟩, fun x ⟨hx, hxy⟩ ↦ ?_⟩, ?_⟩
    · -- `Φ i = e i` is injective on the common source.
      refine (e i).injOn (hsrc ▸ hx) hz ?_
      simp only [hei, mem_preimage, mem_singleton_iff] at hxy ⊢
      rw [hxy, hΦz]
    · -- The inverse of `e i` is differentiable at `y`, so the derivative at `z i` is invertible.
      have hd : DifferentiableAt 𝕜 (e i) ((e i).symm y) := by
        rw [hei]
        exact (hΦi.contDiffAt (hs.mem_nhds (hes hzU))).differentiableAt one_ne_zero
      have hds : DifferentiableAt 𝕜 (e i).symm (e i ((e i).symm y)) := by
        rw [(e i).right_inv hyT]
        exact (hsymmc.contDiffAt ((e i).open_target.mem_nhds hyT)).differentiableAt one_ne_zero
      simpa only [hei] using (e i).isInvertible_fderiv hz hd hds

/-- **Persistence of the solutions in a compact set.** Let `Φ i → Φ₀` in `C¹` at every point of an
open set `s`, with the maps `Φ i` eventually `C¹` on `s`, and let `K ⊆ s` be compact. Suppose that
every solution of `Φ₀ x = y` in `K` lies in the interior of `K` and is nondegenerate. Then there are
points `z i x`, converging to `x` along `l` for every solution `x` of `Φ₀ x = y` in `K`, such that
eventually along `l` the map `x ↦ z i x` is a bijection from the solutions of `Φ₀ x = y` in `K`
onto the solutions of `Φ i x = y` in `K`, and `D Φ i` is invertible at each of the latter. -/
theorem exists_tendsto_bijOn_inter_preimage_singleton_of_tendstoContDiffAt (hs : IsOpen s)
    (hK : IsCompact K) (hKs : K ⊆ s) (hΦ : ∀ᶠ i in l, ContDiffOn 𝕜 1 (Φ i) s)
    (hΦ₀ : ContDiffOn 𝕜 1 Φ₀ s) (hconv : ∀ x ∈ s, TendstoContDiffAt 𝕜 1 Φ Φ₀ l x)
    (hint : K ∩ Φ₀ ⁻¹' {y} ⊆ interior K)
    (hinv : ∀ x ∈ K ∩ Φ₀ ⁻¹' {y}, (fderiv 𝕜 Φ₀ x).IsInvertible) :
    ∃ z : ι → E → E, (∀ x ∈ K ∩ Φ₀ ⁻¹' {y}, Tendsto (fun i ↦ z i x) l (𝓝 x)) ∧
      ∀ᶠ i in l, BijOn (z i) (K ∩ Φ₀ ⁻¹' {y}) (K ∩ Φ i ⁻¹' {y}) ∧
        ∀ x ∈ K ∩ Φ i ⁻¹' {y}, (fderiv 𝕜 (Φ i) x).IsInvertible := by
  set Z := K ∩ Φ₀ ⁻¹' {y}
  have hZfin : Z.Finite := hK.finite_inter_preimage_of_differentiableAt_of_isInvertible
    (hΦ₀.continuousOn.mono hKs)
    (fun x hx ↦ (hΦ₀.contDiffAt (hs.mem_nhds (hKs hx.1))).differentiableAt one_ne_zero) hinv
  -- Disjoint open neighbourhoods `V x` of the finitely many solutions for `Φ₀`.
  obtain ⟨V, hV, hVdisj⟩ := hZfin.t2_separation
  -- Around each solution, it persists uniquely in a neighbourhood `U x ⊆ V x ∩ interior K`.
  have hloc : ∀ x ∈ Z, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ s ∩ interior K ∩ V x ∧
      ∃ w : ι → E, Tendsto w l (𝓝 x) ∧
        ∀ᶠ i in l, U ∩ Φ i ⁻¹' {y} = {w i} ∧ (fderiv 𝕜 (Φ i) (w i)).IsInvertible := by
    intro x hx
    have hs' : IsOpen (s ∩ interior K ∩ V x) := (hs.inter isOpen_interior).inter (hV x).2
    have hxs' : x ∈ s ∩ interior K ∩ V x := ⟨⟨hKs hx.1, hint hx⟩, (hV x).1⟩
    obtain ⟨U, hU, hxU, hUs, -, w, hw, hev⟩ :=
      exists_tendsto_inter_preimage_singleton_eq_singleton_of_tendstoContDiffAt hs' hxs'
        (hΦ.mono fun i hi ↦ hi.mono fun y hy ↦ hy.1.1) (hΦ₀.mono fun y hy ↦ hy.1.1)
        (fun y hy ↦ hconv y hy.1.1) hx.2 (hinv x hx)
    exact ⟨U, hU, hxU, hUs, w, hw, hev⟩
  choose! U hU hxU hUs w hw hev using hloc
  -- Off the neighbourhoods `U x`, the maps `Φ i` eventually do not take the value `y` on `K`.
  have haway : ∀ᶠ i in l, ∀ a ∈ K \ ⋃ x ∈ Z, U x, Φ i a ∈ ({y}ᶜ : Set F) :=
    (hK.diff (isOpen_biUnion fun x hx ↦ hU x hx)).eventually_forall_mem_of_tendsto_prod_nhds
      isOpen_compl_singleton (fun a ha ↦ (hconv a (hKs ha.1)).tendsto)
      fun a ha hay ↦ ha.2 (mem_biUnion ⟨ha.1, hay⟩ (hxU a ⟨ha.1, hay⟩))
  refine ⟨fun i x ↦ w x i, fun x hx ↦ hw x hx, ?_⟩
  filter_upwards [haway, (hZfin.eventually_all (p := fun x i ↦ U x ∩ Φ i ⁻¹' {y} = {w x i} ∧
    (fderiv 𝕜 (Φ i) (w x i)).IsInvertible)).2 hev] with i hi hall
  -- The solution `w x i` of `Φ i x = y` is the only one in `U x`.
  have hmem (x : E) (hx : x ∈ Z) : w x i ∈ U x ∩ Φ i ⁻¹' {y} := by
    rw [(hall x hx).1]
    exact mem_singleton _
  -- Every solution of `Φ i x = y` in `K` lies in some `U x`, hence is some `w x i`.
  have hsurj : ∀ y' ∈ K ∩ Φ i ⁻¹' {y}, ∃ x ∈ Z, w x i = y' := fun y' ⟨hyK, hyy⟩ ↦ by
    by_contra hne
    simp only [not_exists, not_and] at hne
    refine hi y' ⟨hyK, fun hyU ↦ ?_⟩ hyy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyU
    have h : y' ∈ U x ∩ Φ i ⁻¹' {y} := ⟨hyx, hyy⟩
    rw [(hall x hx).1] at h
    exact hne x hx h.symm
  refine ⟨⟨fun x hx ↦ ⟨interior_subset (hUs x hx (hmem x hx).1).1.2, (hmem x hx).2⟩,
    fun x hx x' hx' hxx' ↦ ?_, hsurj⟩, fun y' hy' ↦ ?_⟩
  · -- Distinct solutions for `Φ₀` have disjoint neighbourhoods `V x`.
    by_contra hne
    exact (hVdisj hx hx' hne).ne_of_mem ((hUs x hx (hmem x hx).1).2)
      ((hUs x' hx' (hmem x' hx').1).2) hxx'
  · obtain ⟨x, hx, rfl⟩ := hsurj y' hy'
    exact (hall x hx).2

/-- **The number of solutions in a compact set is eventually constant.** Under the hypotheses of
`TauCeti.exists_tendsto_bijOn_inter_preimage_singleton_of_tendstoContDiffAt`, eventually along `l`
the equation `Φ i x = y` has as many solutions in `K` as `Φ₀ x = y`. -/
theorem eventually_ncard_inter_preimage_singleton_eq_of_tendstoContDiffAt (hs : IsOpen s)
    (hK : IsCompact K) (hKs : K ⊆ s) (hΦ : ∀ᶠ i in l, ContDiffOn 𝕜 1 (Φ i) s)
    (hΦ₀ : ContDiffOn 𝕜 1 Φ₀ s) (hconv : ∀ x ∈ s, TendstoContDiffAt 𝕜 1 Φ Φ₀ l x)
    (hint : K ∩ Φ₀ ⁻¹' {y} ⊆ interior K)
    (hinv : ∀ x ∈ K ∩ Φ₀ ⁻¹' {y}, (fderiv 𝕜 Φ₀ x).IsInvertible) :
    ∀ᶠ i in l, (K ∩ Φ i ⁻¹' {y}).ncard = (K ∩ Φ₀ ⁻¹' {y}).ncard := by
  obtain ⟨z, -, hev⟩ := exists_tendsto_bijOn_inter_preimage_singleton_of_tendstoContDiffAt
    hs hK hKs hΦ hΦ₀ hconv hint hinv
  filter_upwards [hev] with i hi
  rw [← hi.1.image_eq, hi.1.injOn.ncard_image]

end TauCeti
