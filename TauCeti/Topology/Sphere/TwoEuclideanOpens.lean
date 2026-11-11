/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import TauCeti.Topology.CellularSet.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Geometry.Manifold.LocallyFlat.TwoEuclideanOpens
import TauCeti.Topology.CellularSet.InverseSet
import TauCeti.Topology.Compactification.OnePoint.Collapse

/-!
# A compact space covered by two Euclidean open sets is a sphere

Let `X` be a compact Hausdorff space covered by two open sets `U` and `V`, each homeomorphic to a
finite-dimensional real normed space `E` of dimension `m`, with `V ≠ X`. Then `X` is homeomorphic
to the sphere `Sᵐ` (`TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`). In positive
dimension the condition `V ≠ X` holds automatically, since `X` is compact and `E` is not. This is
the topological recognition statement of Milnor (1959, Corollary 1) and Rosen (1960, Lemma 1); it
identifies, for instance, a compact manifold carrying a smooth function with exactly two critical
points as a sphere.

The proof collapses the compact set `K = X \ V`. The map `X → OnePoint V` which is the identity on
`V` and sends `K` to the point at infinity is a continuous surjection collapsing exactly `K`
(`TauCeti.onePointCollapse`), and `OnePoint V ≃ₜ OnePoint E ≃ₜ Sᵐ`. So `X` is a sphere as soon as
collapsing `K` does not change `X`, which holds when `K` is cellular in the chart `U`
(`TauCeti.IsCellularSet.nonempty_homeomorph_of_isOpenEmbedding`); this reduction is
`TauCeti.nonempty_homeomorph_onePoint_of_isCellularSet`. That `K` is cellular is shown dimension by
dimension.

* In dimension `m ≥ 2`, read the collapse in the coordinates of `U`, rescaled so that `K` lies in
  the open unit ball. It is a map of the closed unit ball into `Sᵐ` whose only fibre with more than
  one point is `K`, so `K` is cellular by M. Brown's theorem on inverse sets
  (`TauCeti.isCellularSet_closedBall_inter_preimage`).
* In dimension `1`, `K` is an interval in the coordinates of `U`. A gap of `K` would be carried
  into `V` onto a set which is open and closed in the connected set `V`, hence onto all of `V`;
  then `U` would be the whole compact space `X`.
* In dimension `0`, `K` is the single point of `E`.

No form of the generalized Schoenflies theorem is used.

## Main results

* `TauCeti.nonempty_homeomorph_onePoint_of_isCellularSet`: if the complement of an open set `V`
  of a compact Hausdorff space `X` is cellular in a Euclidean chart, then `X` is homeomorphic to
  the one-point compactification of `V`.
* `TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`: a compact Hausdorff space covered by
  two open sets homeomorphic to `E`, one of them proper, is homeomorphic to the unit sphere of
  `EuclideanSpace ℝ ι` for `ι` with `dim E + 1` elements.

## References

* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), 439–444, Theorem 1 and Corollary 1.
* R. H. Rosen, *A weak form of the star conjecture for manifolds*, Notices Amer. Math. Soc. 7
  (1960), abstract 570-28, p. 380, Lemma 1.
* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorems 0 and 3 (cellular sets and their collapse, and the inverse set theorem).
-/

public section

open Function Metric Module Set Topology OnePoint

namespace TauCeti

variable {X E F W : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace W]
  {U V : Set X}

/-- **The one-point compactification of an open set with cellular complement.** Let `X` be a
compact Hausdorff space and `V ⊆ X` an open set homeomorphic to a locally compact Hausdorff space
`W`, with `V ≠ X`. If the complement `X \ V` lies in the range of an open embedding `θ : F → X` of
a finite-dimensional real normed space and `θ ⁻¹' (X \ V)` is cellular in `F`, then `X` is
homeomorphic to the one-point compactification of `W`. -/
theorem nonempty_homeomorph_onePoint_of_isCellularSet [CompactSpace X] [T2Space X]
    [LocallyCompactSpace W] [T2Space W] (hV : IsOpen V) (hVX : V ≠ univ) (eV : V ≃ₜ W)
    {θ : F → X} (hθ : IsOpenEmbedding θ) (hVθ : Vᶜ ⊆ range θ) (hK : IsCellularSet F (θ ⁻¹' Vᶜ)) :
    Nonempty (X ≃ₜ OnePoint W) := by
  -- The collapse `X → OnePoint W` along `eV⁻¹` collapses exactly `X \ V`.
  have he : IsOpenEmbedding (Subtype.val ∘ eV.symm) :=
    hV.isOpenEmbedding_subtypeVal.comp eV.symm.isOpenEmbedding
  have hr : range (Subtype.val ∘ eV.symm) = V := by rw [EquivLike.range_comp, Subtype.range_coe]
  refine hK.nonempty_homeomorph_of_isOpenEmbedding hθ hVθ
    (continuous_onePointCollapse he isProperMap_id)
    (surjective_onePointCollapse he.injective surjective_id (by rwa [hr])) fun x y ↦ ?_
  rw [onePointCollapse_eq_onePointCollapse_iff he.injective injective_id, hr]
  rfl

/-- In dimension one: if `θ : ℝ → X` is an open embedding into a compact space whose range,
together with a preconnected open set `V ≠ X`, covers `X`, then `θ ⁻¹' (X \ V)` is a closed
interval, hence cellular. -/
private theorem isCellularSet_preimage_compl_of_real [CompactSpace X] [T2Space X] {θ : ℝ → X}
    (hθ : IsOpenEmbedding θ) (hV : IsOpen V) (hVc : IsPreconnected V) (hθV : range θ ∪ V = univ)
    (hVX : V ≠ univ) : IsCellularSet ℝ (θ ⁻¹' Vᶜ) := by
  set S := θ ⁻¹' Vᶜ
  have hVθ : Vᶜ ⊆ range θ := fun x hx ↦ (eq_univ_iff_forall.1 hθV x).resolve_right hx
  have hS : IsCompact S := hθ.isInducing.isCompact_preimage' hV.isClosed_compl.isCompact hVθ
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := (ne_univ_iff_exists_notMem V).1 hVX
    obtain ⟨v, rfl⟩ := hVθ hx
    exact ⟨v, hx⟩
  -- `S` has no gap: the image of a gap `(a₀, b₀)` would be open and closed in `V`, hence all of
  -- `V`, and then `θ` would be onto the compact space `X`.
  have hSc : OrdConnected S := by
    refine ⟨fun a ha b hb c hc ↦ by_contra fun hcS ↦ ?_⟩
    have hSl : IsCompact (S ∩ Iic c) := hS.inter_right isClosed_Iic
    have hSr : IsCompact (S ∩ Ici c) := hS.inter_right isClosed_Ici
    have ha₀ := hSl.sSup_mem ⟨a, ha, hc.1⟩
    have hb₀ := hSr.sInf_mem ⟨b, hb, hc.2⟩
    have hca : sSup (S ∩ Iic c) < c := ha₀.2.lt_of_ne fun h ↦ hcS (h ▸ ha₀.1)
    have hcb : c < sInf (S ∩ Ici c) := hb₀.2.lt_of_ne' fun h ↦ hcS (h ▸ hb₀.1)
    set G := Ioo (sSup (S ∩ Iic c)) (sInf (S ∩ Ici c))
    have hGV {t : ℝ} (ht : t ∈ G) : θ t ∈ V := by
      by_contra htS
      rcases le_total t c with htc | htc
      · exact ht.1.not_ge (le_csSup hSl.bddAbove ⟨htS, htc⟩)
      · exact ht.2.not_ge (csInf_le hSr.bddBelow ⟨htS, htc⟩)
    have hVG : V ⊆ θ '' G := by
      refine hVc.subset_of_closure_inter_subset (hθ.isOpenMap _ isOpen_Ioo)
        ⟨θ c, hGV ⟨hca, hcb⟩, c, ⟨hca, hcb⟩, rfl⟩ ?_
      rintro _ ⟨hx, hxV⟩
      obtain ⟨t, ht, rfl⟩ := closure_minimal (image_mono Ioo_subset_Icc_self)
        (isCompact_Icc.image hθ.continuous).isClosed hx
      refine ⟨t, ⟨ht.1.lt_of_ne ?_, ht.2.lt_of_ne ?_⟩, rfl⟩
      · rintro rfl
        exact ha₀.1 hxV
      · rintro rfl
        exact hb₀.1 hxV
    have hθs : range θ = univ := eq_univ_of_forall fun x ↦
      (eq_univ_iff_forall.1 hθV x).elim id fun hx ↦ image_subset_range _ _ (hVG hx)
    exact noncompact_univ ℝ (by
      simpa using hθ.isInducing.isCompact_preimage' isCompact_univ hθs.ge)
  -- A compact interval is a closed ball.
  have hSI : S = Icc (sInf S) (sSup S) := eq_Icc_csInf_csSup_of_connected_bdd_closed
    ⟨hSne, hSc.isPreconnected⟩ hS.bddBelow hS.bddAbove hS.isClosed
  have hball : closedBall ((sInf S + sSup S) / 2) ((sSup S - sInf S) / 2) = S := by
    rw [Real.closedBall_eq_Icc]
    convert hSI.symm using 2 <;> ring
  have hle : sInf S ≤ sSup S :=
    (csInf_le hS.bddBelow hSne.some_mem).trans (le_csSup hS.bddAbove hSne.some_mem)
  exact hball ▸ isCellularSet_closedBall _ (by linarith)

/-- In dimension at least two: after rescaling the coordinates of `U` so that `X \ V` lies in the
open unit ball, the collapse of `X \ V` is a map of the closed unit ball into the sphere whose only
inverse set is `X \ V`, which is therefore cellular by Brown's theorem on inverse sets. -/
private theorem exists_isCellularSet_preimage_compl_of_two_le [CompactSpace X] [T2Space X]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (hn : 2 ≤ finrank ℝ E)
    (hι : finrank ℝ E + 1 = Fintype.card ι) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (hVX : V ≠ univ) (eU : U ≃ₜ E) (eV : V ≃ₜ E) :
    ∃ θ : E → X, IsOpenEmbedding θ ∧ range θ = U ∧ IsCellularSet E (θ ⁻¹' Vᶜ) := by
  obtain ⟨R, -, hR⟩ := exists_nonneg_forall_notMem_norm_lt hV hUV eU
  obtain ⟨x₀, hx₀⟩ := (ne_univ_iff_exists_notMem V).1 hVX
  have hx₀U : x₀ ∈ U := (eq_univ_iff_forall.1 hUV x₀).resolve_right hx₀
  have hR0 : 0 < R := (norm_nonneg _).trans_lt (hR ⟨x₀, hx₀U⟩ hx₀)
  -- The rescaled chart `θ v = eU⁻¹ (R • v)`, in which `X \ V` lies in the open unit ball.
  set θ : E → X := fun v ↦ eU.symm (R • v)
  have hθ : IsOpenEmbedding θ := hU.isOpenEmbedding_subtypeVal.comp
    (eU.symm.isOpenEmbedding.comp (Homeomorph.smulOfNeZero R hR0.ne').isOpenEmbedding)
  have hθinv {x : X} (hx : x ∈ U) : θ (R⁻¹ • eU ⟨x, hx⟩) = x := by
    simp [θ, smul_smul, hR0.ne']
  have hθr : range θ = U :=
    (range_subset_iff.2 fun v ↦ (eU.symm (R • v)).2).antisymm fun x hx ↦ ⟨_, hθinv hx⟩
  have hθV {v : E} (hv : θ v ∉ V) : ‖v‖ < 1 := by
    have := hR (eU.symm (R • v)) hv
    rwa [Homeomorph.apply_symm_apply, norm_smul, Real.norm_of_nonneg hR0.le,
      mul_lt_iff_lt_one_right hR0] at this
  -- The collapse read through `θ` is a map `f` of the closed unit ball into the sphere whose only
  -- inverse set is `θ ⁻¹' (X \ V)`.
  have he : IsOpenEmbedding (Subtype.val ∘ eV.symm) :=
    hV.isOpenEmbedding_subtypeVal.comp eV.symm.isOpenEmbedding
  have hr : range (Subtype.val ∘ eV.symm) = V := by rw [EquivLike.range_comp, Subtype.range_coe]
  set ψ := onePointEquivSphereOfFinrankEq hι
  set f : E → sphere (0 : EuclideanSpace ℝ ι) 1 :=
    fun v ↦ ψ (onePointCollapse (Subtype.val ∘ eV.symm) id (θ v))
  have hfy (v : E) : f v = ψ ∞ ↔ θ v ∉ V := by
    rw [ψ.injective.eq_iff, onePointCollapse_eq_infty_iff he.injective, hr]
  have hcell := isCellularSet_closedBall_inter_preimage (f := f) (y := ψ ∞) hn
    (by rw [finrank_euclideanSpace, ← hι])
    (ψ.continuous.comp ((continuous_onePointCollapse he isProperMap_id).comp
      hθ.continuous)).continuousOn
    (fun v hv w _ hvw ↦ hθ.injective <| ((onePointCollapse_eq_onePointCollapse_iff he.injective
      injective_id).1 (ψ.injective hvw)).resolve_right fun h ↦ hv.2 ((hfy v).2 (hr ▸ h.1)))
    (fun ⟨v, hv, hfv⟩ ↦ (hθV ((hfy v).1 hfv)).ne (mem_sphere_zero_iff_norm.1 hv))
    ⟨_, mem_closedBall_zero_iff.2 (hθV (by rwa [hθinv hx₀U])).le,
      (hfy _).2 (by rwa [hθinv hx₀U])⟩
  have hpre : closedBall 0 1 ∩ f ⁻¹' {ψ ∞} = θ ⁻¹' Vᶜ := by
    ext v
    simp only [mem_inter_iff, mem_closedBall_zero_iff, mem_preimage, mem_singleton_iff, hfy,
      mem_compl_iff]
    exact ⟨And.right, fun h ↦ ⟨(hθV h).le, h⟩⟩
  exact ⟨θ, hθ, hθr, hpre ▸ hcell⟩

/-- **A compact space covered by two Euclidean open sets is a sphere.** Let `X` be a compact
Hausdorff space covered by two open sets `U` and `V`, each homeomorphic to a finite-dimensional real
normed space `E`, with `V ≠ X`. Then `X` is homeomorphic to the unit sphere of `EuclideanSpace ℝ ι`
for every finite type `ι` with `dim E + 1` elements. When `dim E > 0` the hypothesis `V ≠ X` holds
automatically, since `X` is compact and `E` is not; when `dim E = 0` it excludes the one-point
space. -/
theorem nonempty_homeomorph_sphere_of_two_euclidean_opens [CompactSpace X] [T2Space X]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (hι : finrank ℝ E + 1 = Fintype.card ι)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) (hVX : V ≠ univ) (eU : U ≃ₜ E)
    (eV : V ≃ₜ E) : Nonempty (X ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1) := by
  have hVU : Vᶜ ⊆ U := fun x hx ↦ (eq_univ_iff_forall.1 hUV x).resolve_right hx
  have hθ : IsOpenEmbedding (Subtype.val ∘ eU.symm) :=
    hU.isOpenEmbedding_subtypeVal.comp eU.symm.isOpenEmbedding
  have hθr : range (Subtype.val ∘ eU.symm) = U := by rw [EquivLike.range_comp, Subtype.range_coe]
  -- It suffices that `X \ V` is cellular in some Euclidean chart.
  suffices h : Nonempty (X ≃ₜ OnePoint E) from
    h.map fun h ↦ h.trans (onePointEquivSphereOfFinrankEq hι)
  obtain h0 | h1 | h2 : finrank ℝ E = 0 ∨ finrank ℝ E = 1 ∨ 2 ≤ finrank ℝ E := by omega
  · -- In dimension zero, `X \ V` is read in `U` as the single point of `E`.
    have : Subsingleton E := Module.finrank_zero_iff.1 h0
    obtain ⟨x, hx⟩ := (ne_univ_iff_exists_notMem V).1 hVX
    have hK : (Subtype.val ∘ eU.symm) ⁻¹' Vᶜ = closedBall 0 0 := by
      ext v
      refine iff_of_true ?_ (by simp [Subsingleton.elim v 0])
      rw [mem_preimage, Subsingleton.elim v (eU ⟨x, hVU hx⟩), comp_apply,
        Homeomorph.symm_apply_apply]
      exact hx
    exact nonempty_homeomorph_onePoint_of_isCellularSet hV hVX eV hθ (by rwa [hθr])
      (hK ▸ isCellularSet_closedBall 0 le_rfl)
  · -- In dimension one, read `U` through a homeomorphism with `ℝ`.
    let L : ℝ ≃ₜ E := (ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_self, h1])).toHomeomorph
    have hθ₁ : IsOpenEmbedding ((Subtype.val ∘ eU.symm) ∘ L) := hθ.comp L.isOpenEmbedding
    have hθ₁r : range ((Subtype.val ∘ eU.symm) ∘ L) = U := by
      rw [L.surjective.range_comp, hθr]
    have hVc : IsPreconnected V := by
      have := isPreconnected_range
        (hV.isOpenEmbedding_subtypeVal.comp eV.symm.isOpenEmbedding).continuous
      rwa [EquivLike.range_comp, Subtype.range_coe] at this
    exact nonempty_homeomorph_onePoint_of_isCellularSet hV hVX eV hθ₁ (by rwa [hθ₁r])
      (isCellularSet_preimage_compl_of_real hθ₁ hV hVc (by rw [hθ₁r, hUV]) hVX)
  · obtain ⟨θ, hθ, hθr, hK⟩ :=
      exists_isCellularSet_preimage_compl_of_two_le h2 hι hU hV hUV hVX eU eV
    exact nonempty_homeomorph_onePoint_of_isCellularSet hV hVX eV hθ (by rwa [hθr]) hK

end TauCeti
