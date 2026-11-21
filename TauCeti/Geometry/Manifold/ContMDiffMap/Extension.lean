/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.ContMDiff.Log

/-!
# Extending local smooth data to global smooth maps

Vector-valued data on a closed subset of a smooth manifold extend globally if they
extend smoothly near every point of that subset. The extension can have topological
support inside any prescribed open neighbourhood. This is the partition-of-unity
step in extending velocities from an embedded submanifold to its ambient manifold.

The construction reduces to Mathlib's `exists_contMDiffMap_forall_mem_convex_of_local`, applied
to singleton constraints on the closed set and zero constraints off an open neighbourhood whose
closure lies in the prescribed one.

The pointwise form needs only one bump function: a function that is smooth on a
neighbourhood of a point has the germ there of a globally smooth map
(`ContMDiffOn.exists_contMDiffMap_eventuallyEq`), with no paracompactness assumption.
A smooth map on an open subset, extended arbitrarily outside it, stays smooth on that subset
(`ContMDiffMap.contMDiffOn_extend`), and therefore agrees near any point of the open subset with
the restriction of a global smooth map
(`ContMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val`), or of a globally smooth positive
function when it is positive (`ContMDiff.exists_contMDiffMap_pos_eventuallyEq_comp_subtype_val`).
For manifold-valued maps on an open star-convex subset of a finite-dimensional real space,
`ContMDiffOn.exists_contMDiff_eventuallyEq_of_starConvex` gives a global map agreeing near
any set closed in the ambient real space and contained in the domain.
A closed set inside an open set has a smooth `[0, 1]`-valued cutoff equal to one exactly on the
closed set, with topological support in the open set
(`IsClosed.exists_contMDiff_tsupport_subset_eq_one_iff`).
Reference: M. Hirsch, *Differential Topology*, Chapter 2, §2, and Chapter 8, §1.
-/

public section

open Set Function Topology
open scoped Manifold ContDiff

namespace ContMDiffMap

variable {𝕜 E E' H H' M M' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M'] {n : ℕ∞ω}

/-- Extending a smooth map on an open subset arbitrarily outside that subset gives a map that is
smooth on the subset. -/
theorem contMDiffOn_extend (U : TopologicalSpace.Opens M) (f : C^n⟮I, U; I', M'⟯) (g : M → M') :
    ContMDiffOn I I' n (Function.extend Subtype.val f g) U := fun x hx ↦ by
  refine (contMDiffAt_subtype_iff (x := ⟨x, hx⟩)).mp ?_ |>.contMDiffWithinAt
  rw [show (fun z : U ↦ extend Subtype.val f g z) = f from extend_comp Subtype.val_injective _ _]
  exact f.contMDiff _

end ContMDiffMap

section Cutoff

variable {𝕜 E E' F H H' M P : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- A product `ψ • g` is `C^n` on the whole manifold when `ψ` and `g` are `C^n` on an open set `s`
containing the topological support of `ψ`: multiplying by a cutoff `ψ` globalizes a vector-valued
map defined on `s`. -/
theorem ContMDiffOn.contMDiff_smul_of_tsupport_subset {ψ : M → 𝕜} {g : M → F} {s : Set M}
    (hg : ContMDiffOn I 𝓘(𝕜, F) n g s) (hs : IsOpen s)
    (hψ : ContMDiffOn I 𝓘(𝕜) n ψ s) (hψs : tsupport ψ ⊆ s) :
    ContMDiff I 𝓘(𝕜, F) n (fun x ↦ ψ x • g x) := by
  refine contMDiff_of_tsupport fun x hx ↦ ?_
  have hxs : x ∈ s := hψs (tsupport_smul_subset_left ψ g hx)
  exact (hψ.contMDiffAt (hs.mem_nhds hxs)).smul (hg.contMDiffAt (hs.mem_nhds hxs))

/-- A product `(x, p) ↦ ψ x • g (x, p)` is `C^n` on the product manifold `M × P` when `ψ` is `C^n`
on an open set `s ⊆ M` containing `tsupport ψ` and `g` is `C^n` on `s ×ˢ univ`: multiplying by a
cutoff on the base globalizes a parameterized family defined on `s ×ˢ univ`. -/
theorem ContMDiffOn.contMDiff_smul_fst_of_tsupport_subset
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
    [TopologicalSpace P] [ChartedSpace H' P]
    {ψ : M → 𝕜} {g : M × P → F} {s : Set M}
    (hg : ContMDiffOn (I.prod J) 𝓘(𝕜, F) n g (s ×ˢ univ)) (hs : IsOpen s)
    (hψ : ContMDiffOn I 𝓘(𝕜) n ψ s) (hψs : tsupport ψ ⊆ s) :
    ContMDiff (I.prod J) 𝓘(𝕜, F) n (fun p : M × P ↦ ψ p.1 • g p) := by
  refine hg.contMDiff_smul_of_tsupport_subset (hs.prod isOpen_univ)
    (hψ.comp contMDiff_fst.contMDiffOn mapsTo_fst_prod) ?_
  exact (closure_minimal (t := tsupport ψ ×ˢ (univ : Set P))
    (fun p hp ↦ ⟨subset_tsupport ψ hp, mem_univ p.2⟩)
    ((isClosed_tsupport ψ).prod isClosed_univ)).trans (prod_mono hψs subset_rfl)

end Cutoff

/-- A manifold-valued `C^n` map on an open star-convex subset of a finite-dimensional real
space agrees near any set closed in the ambient space and contained in the domain with a
globally `C^n` map. -/
theorem ContMDiffOn.exists_contMDiff_eventuallyEq_of_starConvex
    {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ∞}
    {γ : F → M} {U K : Set F} {c : F} (hγ : ContMDiffOn 𝓘(ℝ, F) I n γ U)
    (hU : IsOpen U) (hstar : StarConvex ℝ c U)
    (hK : IsClosed K) (hKU : K ⊆ U) :
    ∃ f : F → M, ContMDiff 𝓘(ℝ, F) I n f ∧ ∀ t ∈ K, f =ᶠ[𝓝 t] γ := by
  rcases U.eq_empty_or_nonempty with rfl | hU₀
  · exact ⟨fun _ ↦ γ c, contMDiff_const, fun t ht ↦ (hKU ht).elim⟩
  have hc : c ∈ U := hstar.mem hU₀
  obtain ⟨ρ, hρ1, hρ0, hρI⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ, F) hK (by rwa [hU.interior_eq]) (n := n)
  have hφU (x : F) : c + ρ x • (x - c) ∈ U := by
    by_cases hx : x ∈ U
    · exact hstar.add_smul_sub_mem hx (hρI x).1 (hρI x).2
    · simp [hρ0 x hx, hc]
  refine ⟨fun x ↦ γ (c + ρ x • (x - c)), fun x ↦ ?_, fun t ht ↦ ?_⟩
  · exact (hγ.contMDiffAt (hU.mem_nhds (hφU x))).comp x
      (contMDiff_const.add (ρ.contMDiff.smul (contMDiff_id.sub contMDiff_const))).contMDiffAt
  · filter_upwards [eventually_nhdsSet_iff_forall.1 hρ1 t ht] with x hx
    simp [hx]

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {n : ℕ∞}

/-- **A smooth germ is the germ of a global smooth map.** A vector-valued function that is `C^n`
on a neighbourhood of a point agrees near that point with a globally `C^n` map, namely its
product with a smooth bump function supported in that neighbourhood. -/
theorem ContMDiffOn.exists_contMDiffMap_eventuallyEq {U : Set M} {g : M → F} {x : M}
    (hg : ContMDiffOn I 𝓘(ℝ, F) n g U) (hU : U ∈ 𝓝 x) :
    ∃ G : C^n⟮I, M; 𝓘(ℝ, F), F⟯, (G : M → F) =ᶠ[𝓝 x] g := by
  have hU' : interior U ∈ 𝓝 x := interior_mem_nhds.mpr hU
  obtain ⟨β, hβ, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hU').mem_iff.mp hU'
  refine ⟨⟨fun y ↦ β y • g y, contMDiff_of_tsupport fun y hy ↦ ?_⟩, ?_⟩
  · exact β.contMDiffAt.of_le (mod_cast le_top) |>.smul <| hg.contMDiffAt <|
      mem_interior_iff_mem_nhds.mp <| hβ <| tsupport_smul_subset_left _ _ hy
  · filter_upwards [β.eventuallyEq_one] with y hy
    simp [hy]

/-- **Smooth germ extension from an open submanifold.** A `C^n` vector-valued function on an open
submanifold `U` agrees near any point `x : U` with the restriction `G ∘ Subtype.val` of a globally
`C^n` map `G : C^n⟮I, M; 𝓘(ℝ, F), F⟯`. -/
theorem ContMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val
    {U : TopologicalSpace.Opens M} {φ : U → F} {x : U} (hφ : ContMDiff I 𝓘(ℝ, F) n φ) :
    ∃ G : C^n⟮I, M; 𝓘(ℝ, F), F⟯, ((G : M → F) ∘ Subtype.val) =ᶠ[𝓝 x] φ := by
  obtain ⟨G, hG_eq⟩ := (ContMDiffMap.contMDiffOn_extend U ⟨φ, hφ⟩
    0).exists_contMDiffMap_eventuallyEq (U.isOpen.mem_nhds x.property)
  refine ⟨G, ((continuous_subtypeVal.tendsto x).eventually hG_eq).mono fun y hy ↦ ?_⟩
  simpa [Subtype.val_injective.extend_apply] using hy

/-- **Positive smooth germ extension from an open submanifold.** A positive `C^n` function on an
open submanifold `U` agrees near any point `x : U` with the restriction `G ∘ Subtype.val` of a
globally `C^n` positive function `G : C^n⟮I, M; 𝓘(ℝ), ℝ⟯`, obtained by extending `log ∘ φ` and
exponentiating. -/
theorem ContMDiff.exists_contMDiffMap_pos_eventuallyEq_comp_subtype_val
    {U : TopologicalSpace.Opens M} {φ : U → ℝ} {x : U}
    (hφ : ContMDiff I 𝓘(ℝ) n φ) (hφ_pos : ∀ y, 0 < φ y) :
    ∃ G : C^n⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ y, 0 < G y) ∧ ((G : M → ℝ) ∘ Subtype.val) =ᶠ[𝓝 x] φ := by
  obtain ⟨H, hH_eq⟩ :=
    (hφ.log fun y ↦ (hφ_pos y).ne').exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
  refine ⟨⟨fun y ↦ Real.exp (H y), Real.contDiff_exp.comp_contMDiff H.contMDiff⟩,
    fun y ↦ Real.exp_pos _, hH_eq.mono fun y hy ↦ ?_⟩
  simp only [ContMDiffMap.coeFn_mk, Function.comp_apply] at hy ⊢
  rw [hy, Real.exp_log (hφ_pos y)]

/-- Locally smoothly extendible vector-valued data on a closed set have a global
`C^n` extension supported inside any prescribed open neighbourhood of that set.
No regularity is required of the original function away from the closed set. -/
theorem IsClosed.exists_contMDiffMap_eqOn [SigmaCompactSpace M] {s U : Set M} (hs : IsClosed s)
    {g : M → F} (hU : IsOpen U) (hsU : s ⊆ U)
    (hloc : ∀ x ∈ s, ∃ V ∈ 𝓝 x, ∃ g' : M → F, ContMDiffOn I 𝓘(ℝ, F) n g' V ∧ EqOn g' g (s ∩ V)) :
    ∃ G : C^n⟮I, M; 𝓘(ℝ, F), F⟯, EqOn G g s ∧ tsupport G ⊆ U := by
  classical
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- Ask for the value of `g` on `s`, anything on `W`, and zero off `W`, where `closure W ⊆ U`.
  obtain ⟨W, hWo, hsW, hWU⟩ := normal_exists_closure_subset hs hU hsU
  obtain ⟨G, hG⟩ := exists_contMDiffMap_forall_mem_convex_of_local (n := n) I
    (t := fun y ↦ if y ∈ s then {g y} else if y ∈ W then univ else {0})
    (fun y ↦ by split_ifs <;> first | exact convex_singleton _ | exact convex_univ) fun x ↦ by
      by_cases hx : x ∈ s
      · obtain ⟨V, hV, g', hg', heq⟩ := hloc x hx
        refine ⟨V ∩ W, Filter.inter_mem hV (hWo.mem_nhds (hsW hx)), g',
          hg'.mono inter_subset_left, ?_⟩
        rintro y ⟨hyV, hyW⟩
        split_ifs with hys
        exacts [heq ⟨hys, hyV⟩, mem_univ _]
      · refine ⟨sᶜ, hs.isOpen_compl.mem_nhds hx, 0, contMDiffOn_const, fun y hy ↦ ?_⟩
        split_ifs <;> simp_all
  refine ⟨G, fun x hx ↦ by simpa [hx] using hG x, (closure_mono fun x hx ↦ ?_).trans hWU⟩
  by_contra hxW
  have hxs : x ∉ s := fun h ↦ hxW (hsW h)
  exact mem_support.mp hx (by simpa [hxs, hxW] using hG x)

/-- **Smooth cutoffs.** A closed set inside an open set of a Hausdorff sigma-compact manifold has
a smooth cutoff with values in `[0, 1]`, topological support in the open set, and equal to one
exactly on the closed set. -/
theorem IsClosed.exists_contMDiff_tsupport_subset_eq_one_iff [SigmaCompactSpace M] {A U : Set M}
    (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ ρ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ ρ ∧ (∀ x, ρ x ∈ Icc 0 1) ∧ tsupport ρ ⊆ U ∧
      ∀ x, x ∈ A ↔ ρ x = 1 := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- Take Mathlib's cutoff with support an open `V` whose closure lies in `U`.
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA hU hAU
  obtain ⟨ρ, hsρ, hrange, hsupp, hone⟩ := exists_contMDiff_support_eq_eq_one_iff I hV hA hAV
  refine ⟨ρ, hsρ, fun x ↦ hrange (mem_range_self x), ?_, hone⟩
  rw [tsupport, hsupp]
  exact hVU
