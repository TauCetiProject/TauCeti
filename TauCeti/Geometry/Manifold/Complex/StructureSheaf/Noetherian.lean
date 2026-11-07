/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.RingTheory.FiniteType
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
import TauCeti.RingTheory.Ideal.Quotient.Finite

/-!
# Holomorphic stalks are Noetherian

The ring `𝒪_{X, x}` of germs of holomorphic functions at a point of a finite-dimensional complex
manifold without boundary is Noetherian. In a chart this is the ring of convergent power series
in `n` variables, and the proof is the classical induction on `n` through Weierstrass preparation.

For `n = 0` the stalk is `ℂ`. For the inductive step on `E × ℂ`, an ideal other than `0` and the
unit ideal contains a nonzero germ `f` vanishing at `p`. Its restriction to some line through `p`
does not vanish identically
(`AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul`). After a linear change
of coordinates taking the last axis to that line, `f` is regular in the last variable, so by
Weierstrass preparation the quotient `𝒪_{E × ℂ, p} ⧸ (f)` is a finite module over the Noetherian
ring `𝒪_{E, p.1}` (`TauCeti.holomorphicStructureSheaf.finite_quotientMk_comp_stalkPrecomp_fst`).
An ideal containing `f` is then finitely generated (`Ideal.fg_of_le_of_finite_quotient`).

Every finite-dimensional complex normed space is linearly isomorphic to some `(Fin n → ℂ) × ℂ` or
is zero, and charts identify the stalks of a manifold with those of its model, so the result
holds on every finite-dimensional complex manifold without boundary. Through the comparison of
holomorphic and complex-smooth germs, the same holds for the stalks of Mathlib's complex-smooth
structure sheaf.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.stalkIsNoetherianRing`: holomorphic stalks are Noetherian.
* `TauCeti.holomorphicStructureSheaf.smoothStalkIsNoetherianRing`: so are the stalks of the
  complex-smooth structure sheaf.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter VI.
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
* H. Grauert, R. Remmert, *Coherent Analytic Sheaves*, Ch. 2.
-/

public noncomputable section

open Filter Module Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section NormedSpace

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- On a zero-dimensional space, evaluation identifies every holomorphic stalk with `ℂ`. -/
private theorem isNoetherianRing_stalk_of_finrank_eq_zero [FiniteDimensional ℂ V]
    (hV : finrank ℂ V = 0) (x : V) :
    IsNoetherianRing ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x) := by
  have hV' : ∀ y : V, y = x := fun y ↦
    (finrank_zero_iff_forall_zero.1 hV y).trans (finrank_zero_iff_forall_zero.1 hV x).symm
  refine isNoetherianRing_of_ringEquiv ℂ (RingEquiv.ofBijective (eval 𝓘(ℂ, V) V x)
    ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ ?_, eval_surjective _ _ x⟩).symm
  obtain ⟨φ, -, hφ⟩ := exists_toFilterGerm_eq x s
  apply toFilterGerm_nhds_injective x
  rw [hφ, map_zero, ← Germ.coe_zero, Germ.coe_eq]
  refine Eventually.of_forall fun y ↦ ?_
  rw [hV' y, ← eval_eq_of_toFilterGerm_eq (hφ _ le_rfl), hs, Pi.zero_apply]

/-- If the holomorphic stalks of `V` are Noetherian, so are those of `V × ℂ`: an ideal containing
a nonzero nonunit germ is finitely generated because, after a linear change of coordinates making
the germ regular in the last variable, the quotient by the germ is finite over a stalk of `V` by
Weierstrass preparation. -/
private theorem isNoetherianRing_stalk_prod [FiniteDimensional ℂ V]
    (hV : ∀ x : V, IsNoetherianRing ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x))
    (p : V × ℂ) :
    IsNoetherianRing ((holomorphicStructureSheaf 𝓘(ℂ, V × ℂ) (V × ℂ)).presheaf.stalk p) := by
  refine (isNoetherianRing_iff_ideal_fg _).2 fun I ↦ ?_
  rcases eq_or_ne I ⊤ with rfl | hI
  · exact ⟨{1}, by simp⟩
  rcases eq_or_ne I ⊥ with rfl | hI₀
  · exact Submodule.fg_bot
  obtain ⟨f, hfI, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI₀
  obtain ⟨F, hF, hfF⟩ := exists_analyticAt_toFilterGerm_eq p f
  have hFp : F p = 0 := by
    rw [← eval_eq_of_toFilterGerm_eq (hfF _ le_rfl)]
    simpa using fun hu ↦ hI (I.eq_top_of_isUnit_mem hfI hu)
  -- Some line through `p` meets the zero set of `F` in a discrete set; its direction `v` is
  -- nonzero since `F p = 0`.
  obtain ⟨v, hv⟩ : ∃ v, ¬(fun t : ℂ ↦ F (p + t • v)) =ᶠ[𝓝 0] 0 := by
    by_contra! h
    refine hf (toFilterGerm_nhds_injective p ?_)
    rw [hfF _ le_rfl, map_zero, ← Germ.coe_zero, Germ.coe_eq]
    exact hF.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul.2 h
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (Eventually.of_forall fun t ↦ by simp [hFp])
  -- Move to linear coordinates in which `v` is the last axis.
  obtain ⟨L, hL⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq (R := ℂ)
    (x := ((0 : V), (1 : ℂ))) (by simp) hv0
  obtain ⟨⟨x₀, w₀⟩, rfl⟩ : ∃ q, L q = p := ⟨L.symm p, L.apply_symm_apply p⟩
  let σ := RingEquiv.ofBijective _ (L.holomorphicStalkPullback_bijective (x₀, w₀))
  have hσf : toFilterGerm 𝓘(ℂ, V × ℂ) (V × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl (σ f) = ↑(F ∘ L) := by
    simp only [σ, RingEquiv.ofBijective_apply, toFilterGerm_stalkPullback, hfF _ le_rfl,
      Germ.coe_compTendsto]
  -- The vertical slice of `σ f` is the restriction of `F` to the line through `p` along `v`.
  have hslice : analyticOrderAt (fun w ↦ F (L (x₀, w))) w₀ ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    refine fun h ↦ hv ?_
    have ht : Tendsto (fun t : ℂ ↦ w₀ + t) (𝓝 0) (𝓝 w₀) := by
      have : Continuous fun t : ℂ ↦ w₀ + t := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [ht.eventually h] with t ht
    have hLt : L (x₀, w₀ + t) = L (x₀, w₀) + t • v := by
      rw [← hL, ← L.map_smul, ← L.map_add]
      simp
    simpa [hLt] using ht
  have hπ : ContMDiff 𝓘(ℂ, V × ℂ) 𝓘(ℂ, V) ω Prod.fst := contMDiff_iff_contDiff.2 contDiff_fst
  have hfin := finite_quotientMk_comp_stalkPrecomp_fst hπ
    ((map_residue_verticalPowerSeries_ne_zero_iff hσf).2 hslice)
  -- The transported ideal contains `σ f`, modulo which the stalk is finite over `𝒪_{V, x₀}`.
  algebraize [stalkPrecomp 𝓘(ℂ, V × ℂ) (V × ℂ) Prod.fst hπ (x₀, w₀)]
  have : Module.Finite ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x₀)
      ((holomorphicStructureSheaf 𝓘(ℂ, V × ℂ) (V × ℂ)).presheaf.stalk (x₀, w₀) ⧸
        Ideal.span {σ f}) :=
    RingHom.finite_algebraMap.1 hfin
  have hσI := Ideal.fg_of_le_of_finite_quotient
    (A := (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x₀)
    (Submodule.fg_span_singleton (σ f))
    ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_map_of_mem σ.toRingHom hfI))
  simpa only [RingEquiv.toRingHom_eq_coe, Ideal.map_of_equiv] using hσI.map σ.symm.toRingHom

/-- Holomorphic stalks of a finite-dimensional complex normed space are Noetherian, by induction
on the dimension. -/
private theorem isNoetherianRing_stalk_of_finrank_eq :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = n → ∀ x : V,
        IsNoetherianRing ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x)
  | 0, _, _, _, _, hV, x => isNoetherianRing_stalk_of_finrank_eq_zero hV x
  | n + 1, V, _, _, _, hV, x => by
    let e : V ≃L[ℂ] (Fin n → ℂ) × ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp [hV])
    have := isNoetherianRing_stalk_prod
      (isNoetherianRing_stalk_of_finrank_eq n (Fin n → ℂ) (by simp)) (e x)
    exact isNoetherianRing_of_surjective _ _ _
      (e.holomorphicStalkPullback_bijective x).2

end NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- The stalk of holomorphic functions at any point of a finite-dimensional complex manifold
without boundary is a Noetherian ring. -/
instance stalkIsNoetherianRing (x : X) :
    IsNoetherianRing ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  -- The model `E` may live in any universe, while the stalks of the model spaces compared above
  -- live in `Type`: compose the chart at `x` with a linear isomorphism onto a space in `Type`.
  obtain ⟨E', _, _, _, ⟨e⟩⟩ : ∃ (E' : Type) (_ : NormedAddCommGroup E') (_ : NormedSpace ℂ E')
      (_ : FiniteDimensional ℂ E'), Nonempty (E ≃L[ℂ] E') :=
    ⟨Fin (finrank ℂ E) → ℂ, inferInstance, inferInstance, inferInstance,
      ⟨ContinuousLinearEquiv.ofFinrankEq (by simp)⟩⟩
  have := isNoetherianRing_stalk_of_finrank_eq _ E' rfl ((e ∘ extChartAt I x) x)
  exact isNoetherianRing_of_surjective _ _ _ (stalkPullback_comp_extChartAt_bijective x e).2

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a Noetherian ring, via its comparison with holomorphic germs. -/
instance smoothStalkIsNoetherianRing (x : X) :
    IsNoetherianRing ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  isNoetherianRing_of_ringEquiv _ (smoothStalkIso I X x).commRingCatIsoToRingEquiv

end TauCeti.holomorphicStructureSheaf
