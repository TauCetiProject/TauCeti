/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.Bergman.Cochains
import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.Bergman.Lifting
import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.DolbeaultGluing
import TauCeti.Analysis.Fredholm.Schwartz

/-!
# Finiteness of holomorphic Čech `H¹` of a chart cover

Let `X` be a Riemann surface with a finite family of holomorphic charts `e i`, and let
`W'' ≤ W' ≤ W` be three families of opens with `closure (W'' i) ⊆ W' i`, `closure (W' i) ⊆ W i`,
and `closure (W i)` compact inside a coordinate disc `U i` of `e i`. Cocycles are taken in the
frames of a line bundle with holomorphic overlap scalars `g`, as in
`TauCeti.RiemannSurface.ChartBergman`; the structure sheaf is `g = 1`.

The middle projection of the compatible triples `(ξ, ξ', η)` (with `ξ' = ξ + δη` on `W''`) onto
the square-integrable cocycles on `W'` is surjective (`ChartBergman.middleProjection_surjective`),
and restriction of square-integrable cocycles from `W` to `W'` is compact
(`ChartBergman.isCompactOperator_restrictCocycles₁`). By Schwartz's lemma
(`ContinuousLinearMap.exists_finset_forall_eq_add_sub_of_surjective_of_isCompactOperator`),
finitely many cocycles span modulo the cocycles `ξ' - ξ|W'`, and on `W''` each of these is the
coboundary `δη`. Hence:

* `ChartBergman.exists_finset_forall_cocycles₁_eq_add_smul_sub`: finitely many square-integrable
  cocycles on `W'` span all square-integrable cocycles on `W'`, restricted to `W''`, up to
  coboundaries of square-integrable zero-cochains on `W''`.
* `ChartBergman.exists_finset_forall_cocycle_eq_add_smul_sub`: when the `W'' i` cover `X`, the
  same finitely many cocycles span every holomorphic Čech `1`-cocycle on the `W''`, with no
  integrability assumption, up to holomorphic coboundaries on `W''`. So the holomorphic Čech `H¹`
  of the cover `W''`, for the structure sheaf or for a line bundle with these frames, is finite
  dimensional.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14 (Theorem 14.9).
-/

public noncomputable section

open Metric Set TopologicalSpace
open scoped ContDiff ENNReal Manifold

universe u

namespace TauCeti.RiemannSurface.ChartBergman

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [T2Space X] {ι : Type*} [Finite ι]
  {e : ι → OpenPartialHomeomorph X ℂ} {W W' W'' : ι → Opens X}
  {U : ι → Set X} {c : ι → ℂ} {R : ι → ℝ≥0∞}

/-- **Finiteness of Bergman `H¹`** (Forster 14.9). Let `closure (W'' i) ⊆ W' i`,
`closure (W' i) ⊆ W i`, and `closure (W i)` compact inside the coordinate disc `U i`, with the
`W' i` covering `X`. Then finitely many square-integrable cocycles `s` on `W'` span all of them up
to coboundaries on `W''`: every square-integrable cocycle `ξ` on `W'` is `b + δη` on the overlaps
of `W''`, for some `b` in the span of `s` and some square-integrable zero-cochain `η` on `W''`. -/
theorem exists_finset_forall_cocycles₁_eq_add_smul_sub
    (g : ι → ι → X → ℂ)
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hW : ∀ i, (W i : Set X) ⊆ (e i).source)
    (hR : ∀ i, eball (c i) (R i) ⊆ (e i).target)
    (hU : ∀ i, U i = (e i).source ∩ e i ⁻¹' eball (c i) (R i))
    (hKW : ∀ i, IsCompact (closure (W i : Set X)))
    (hWU : ∀ i, closure (W i : Set X) ⊆ U i) (hcov : IsOpenCover W')
    (hW'W : ∀ i, closure (W' i : Set X) ⊆ W i)
    (hIW : ∀ i, closure (W'' i : Set X) ⊆ W' i)
    (hg : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (g i j) (U i ∩ U j))
    (hg_one : ∀ i, ∀ x ∈ W' i, g i i x = 1)
    (hg_mul : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, g i j x * g j k x = g i k x) :
    ∃ s : Finset (cocycles₁ g (subset_source_of_le hW fun i ↦ subset_closure.trans (hW'W i))),
      ∀ ξ : cocycles₁ g (subset_source_of_le hW fun i ↦ subset_closure.trans (hW'W i)),
        ∃ b ∈ Submodule.span ℂ (s : Set (cocycles₁ g
            (subset_source_of_le hW fun i ↦ subset_closure.trans (hW'W i)))),
          ∃ η : (i : ι) → bergmanSpace ℂ ((e i).imageOpens (W'' i)),
            ∀ i j, ∀ x ∈ W'' i ⊓ W'' j,
              BergmanSpace.representative (ξ.val i j) (e i x) =
                BergmanSpace.representative (b.val i j) (e i x) +
                  g i j x • BergmanSpace.representative (η j) (e j x) -
                    BergmanSpace.representative (η i) (e i x) := by
  have := Fintype.ofFinite ι
  have h' (i : ι) : W' i ≤ W i := subset_closure.trans (hW'W i)
  have h'' (i : ι) : W'' i ≤ W' i := subset_closure.trans (hIW i)
  have hKW' (i : ι) : IsCompact (closure (W' i : Set X)) :=
    (hKW i).of_isClosed_subset isClosed_closure ((hW'W i).trans subset_closure)
  -- Schwartz's lemma: the middle projection is onto and `ξ ↦ ξ|W'` is compact, so finitely many
  -- cocycles span modulo the cocycles `ξ' - ξ|W'` of the compatible triples `(ξ, ξ', η)`.
  have hK :
      IsCompactOperator ((restrictCocycles₁ g hW h').comp (outerProjection g hW h' h'')) := by
    rw [ContinuousLinearMap.coe_comp]
    exact (isCompactOperator_restrictCocycles₁ g hW hKW' hW'W).comp_clm _
  -- Explicit instances: instance search through these imported subtypes does not unify.
  have : CompleteSpace (compatibleTriples g hW h' h'') :=
    completeSpace_compatibleTriples g hW h' h''
  have : CompleteSpace (cocycles₁ g (subset_source_of_le hW h')) := completeSpace_cocycles₁ g _
  obtain ⟨s, hs⟩ :=
    ContinuousLinearMap.exists_finset_forall_eq_add_sub_of_surjective_of_isCompactOperator (𝕜 := ℂ)
      (E := compatibleTriples g hW h' h'') (F := cocycles₁ g (subset_source_of_le hW h'))
      (middleProjection g hW h' h'')
      ((restrictCocycles₁ g hW h').comp (outerProjection g hW h' h''))
      (middleProjection_surjective g he hW h' hR hU hKW hWU hcov hIW hg hg_one hg_mul) hK
  refine ⟨s, fun ξ ↦ ?_⟩
  obtain ⟨b, hb, t, rfl⟩ := hs ξ
  obtain ⟨-, -, ht⟩ := (mem_compatibleTriples_iff g hW h' h'').mp t.property
  -- On `W''`, `ξ' - ξ|W' = δη` for the compatible triple `t = (ξ, ξ', η)`.
  refine ⟨b, hb, t.val.2.2, fun i j x hx ↦ ?_⟩
  have hx' := (e i).map_mem_imageOpens (hW i (h' i (h'' i hx.1))) (V := W' i ⊓ W' j)
    ⟨h'' i hx.1, h'' j hx.2⟩
  simp only [Submodule.coe_add, Submodule.coe_sub, Pi.add_apply, Pi.sub_apply,
    ContinuousLinearMap.comp_apply, coe_middleProjection, coe_restrictCocycles₁,
    coe_outerProjection, restrictCochains₁_apply, BergmanSpace.representative_add _ _ hx',
    BergmanSpace.representative_sub _ _ hx', BergmanSpace.representative_restrict _ _ hx',
    ht i j x hx, smul_eq_mul]
  ring

/-- **Finiteness of holomorphic Čech `H¹` of a chart cover** (Forster 14.9). Let
`closure (W'' i) ⊆ W' i`, `closure (W' i) ⊆ W i`, and `closure (W i)` compact inside the coordinate
disc `U i`, with the `W'' i` covering `X`. Then finitely many square-integrable cocycles `s` on
`W'` span the holomorphic Čech `1`-cocycles of the cover `W''` up to holomorphic coboundaries:
every holomorphic `ζ` on the `W'' i ⊓ W'' j` with `ζ i j + g i j • ζ j k = ζ i k` is
`b + δη` there, for some `b` in the span of `s` and holomorphic `η i` on `W'' i`. No integrability
or boundedness of `ζ` is assumed. -/
theorem exists_finset_forall_cocycle_eq_add_smul_sub
    (g : ι → ι → X → ℂ)
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hW : ∀ i, (W i : Set X) ⊆ (e i).source)
    (hR : ∀ i, eball (c i) (R i) ⊆ (e i).target)
    (hU : ∀ i, U i = (e i).source ∩ e i ⁻¹' eball (c i) (R i))
    (hKW : ∀ i, IsCompact (closure (W i : Set X)))
    (hWU : ∀ i, closure (W i : Set X) ⊆ U i)
    (hW'W : ∀ i, closure (W' i : Set X) ⊆ W i)
    (hIW : ∀ i, closure (W'' i : Set X) ⊆ W' i) (hcov : IsOpenCover W'')
    (hg : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (g i j) (U i ∩ U j))
    (hg_one : ∀ i, ∀ x ∈ W' i, g i i x = 1)
    (hg_mul : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, g i j x * g j k x = g i k x) :
    ∃ s : Finset (cocycles₁ g (subset_source_of_le hW fun i ↦ subset_closure.trans (hW'W i))),
      ∀ ζ : ι → ι → X → ℂ, (∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (ζ i j) (W'' i ⊓ W'' j)) →
        (∀ i j k, ∀ x ∈ W'' i ⊓ W'' j ⊓ W'' k, ζ i j x + g i j x • ζ j k x = ζ i k x) →
        ∃ b ∈ Submodule.span ℂ (s : Set (cocycles₁ g
            (subset_source_of_le hW fun i ↦ subset_closure.trans (hW'W i)))),
          ∃ η : ι → X → ℂ, (∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (η i) (W'' i)) ∧
            ∀ i j, ∀ x ∈ W'' i ⊓ W'' j,
              ζ i j x = BergmanSpace.representative (b.val i j) (e i x) +
                g i j x • η j x - η i x := by
  have h' (i : ι) : W' i ≤ W i := subset_closure.trans (hW'W i)
  have h'' (i : ι) : W'' i ≤ W' i := subset_closure.trans (hIW i)
  have hcov' : IsOpenCover W' :=
    IsOpenCover.mk (top_unique (hcov.iSup_eq_top ▸ iSup_mono h''))
  obtain ⟨s, hs⟩ := exists_finset_forall_cocycles₁_eq_add_smul_sub g he hW hR hU hKW hWU hcov'
    hW'W hIW hg hg_one hg_mul
  refine ⟨s, fun ζ hζ hζc ↦ ?_⟩
  have : CompactSpace X := by
    refine ⟨(isCompact_iUnion hKW).of_isClosed_subset isClosed_univ fun x _ ↦ ?_⟩
    obtain ⟨i, hi⟩ := hcov.exists_mem x
    exact mem_iUnion.mpr ⟨i, subset_closure (h' i (h'' i hi))⟩
  -- Extend `ζ` to a holomorphic cocycle `ζ'` on the discs `U i`, up to a coboundary on `W''`.
  obtain ⟨ζ', η₀, hζ', hζ'c, hη₀, hζη₀, -⟩ :=
    exists_mdifferentiableOn_cocycle_eq_add_smul_sub_of_chart_eball he hR hU
      (V := fun i ↦ (W'' i : Set X)) (fun i ↦ (W'' i).isOpen)
      (fun i x hx ↦ hWU i (subset_closure (h' i (h'' i hx)))) hcov.iSup_set_eq_univ hg
      (fun i x hx ↦ hg_one i x (h'' i hx)) hg_mul hζ hζc
  -- Its restriction to `W'` is a square-integrable cocycle, which `s` spans modulo `δ`.
  have hKW' (i : ι) : IsCompact (closure (W' i : Set X)) :=
    (hKW i).of_isClosed_subset isClosed_closure ((hW'W i).trans subset_closure)
  obtain ⟨Z, hZc, hZ⟩ := exists_cocycle_representative_eq g he hKW'
    (fun i ↦ (hW'W i).trans (subset_closure.trans (hWU i))) (fun i ↦ (hW'W i).trans (hW i))
    ζ' hζ' hζ'c
  obtain ⟨b, hb, η, hbη⟩ := hs ⟨Z, hZc⟩
  refine ⟨b, hb, fun i ↦ BergmanSpace.representative (η i) ∘ e i - η₀ i, fun i ↦ ?_,
    fun i j x hx ↦ ?_⟩
  · exact (mdifferentiableOn_representative_comp_chart (he i)
      (fun x hx ↦ hW i (h' i (h'' i hx))) (η i)).sub (hη₀ i)
  · have hZx := hZ i j x ⟨h'' i hx.1, h'' j hx.2⟩
    have hbx := hbη i j x hx
    have hζx := hζη₀ i j x hx
    simp only [Pi.sub_apply, Function.comp_apply, smul_eq_mul] at hbx hζx ⊢
    linear_combination -hζx - hZx + hbx

end TauCeti.RiemannSurface.ChartBergman
