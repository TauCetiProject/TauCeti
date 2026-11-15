/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Irreducible.Basic
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import TauCeti.Geometry.Manifold.LocallyFlat.Schoenflies.Euclidean
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Irreducibility of 3-spheres and 3-space, and reducibility of sphere products

By **Alexander's theorem** (1924) in the PL/smooth category and **Brown's collaring and generalized
Schoenflies theorems** (1960, 1962) in the topological locally flat category, every closed locally
flat embedded 2-sphere in `S³` or `ℝ³` bounds an embedded closed 3-ball. Thus both `S³` and `ℝ³`
satisfy `TauCeti.IsSphereBoundsBall`.

Conversely, any product `X × S²` where `X` is a nonempty `T₁` 1-manifold without boundary — in
particular `S¹ × S²` and punctured 3-space `ℝ³ \ {p} ≃ₜ (0, ∞) × S²` — contains a closed locally
flat slice `{x₀} × S²` onto which the ambient space retracts by the second projection. Since `S²`
is not contractible, that slice cannot extend over `D³`, so `X × S²` fails `IsSphereBoundsBall`.

## Main results

* `TauCeti.isSphereBoundsBall_sphere`: the unit sphere of any 4-dimensional real normed space
  satisfies `IsSphereBoundsBall`.
* `TauCeti.isSphereBoundsBall_sphere_euclideanSpace_fin_four` and
  `TauCeti.isSphereBoundsBall_topCatSphere_three`: **Alexander's theorem** for the standard
  3-sphere `S³ ⊂ ℝ⁴` and `TopCat.sphere 3`.
* `TauCeti.isSphereBoundsBall_of_finrank_eq_three` and
  `TauCeti.isSphereBoundsBall_euclideanSpace_fin_three`: every 3-dimensional real normed space (in
  particular `ℝ³`) satisfies `IsSphereBoundsBall`.
* `TauCeti.not_isSphereBoundsBall_prod_sphere_of_isOpenEmbedding` and
  `TauCeti.not_isSphereBoundsBall_prod_sphere`: `X × S(E)` fails `IsSphereBoundsBall` whenever
  `dim E = 3` and `X` is a nonempty `T₁` space charted on a 1-dimensional real normed space (or
  admitting an open embedding of `ℝ`).
* `TauCeti.not_isSphereBoundsBall_circle_prod_sphere`: `Circle × S(E)` fails `IsSphereBoundsBall`
  when `dim E = 3` (`S¹ × S²` is reducible).
* `TauCeti.not_isSphereBoundsBall_compl_singleton`: punctured 3-space `E \ {p}` fails
  `IsSphereBoundsBall` when `dim E = 3`.

## References

* J. W. Alexander, *On the subdivision of 3-space by a polyhedron*, Proc. Nat. Acad. Sci. U.S.A.
  10 (1924), 6–8.
* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* A. Hatcher, *Notes on Basic 3-Manifold Topology*, Theorem 1.1 and Section 1.1.
-/

public section

open Function Metric Module Set Topology

universe u v

namespace TauCeti

/-! ### Irreducibility of `S³` and `ℝ³` -/

/-- **The Alexander–Brown theorem on 3-spheres.** The unit sphere of any 4-dimensional real normed
space satisfies `IsSphereBoundsBall`: every closed locally flat embedded 2-sphere bounds a closed
embedded 3-ball. -/
theorem isSphereBoundsBall_sphere {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hF : finrank ℝ F = 4) : IsSphereBoundsBall (sphere (0 : F) 1) := by
  rw [isSphereBoundsBall_iff_sphere_closedBall]
  intro f _ hf_lf
  have hEG : finrank ℝ (EuclideanSpace ℝ (Fin 3)) = finrank ℝ (EuclideanSpace ℝ (Fin 2)) + 1 := by
    simp
  have hEF : finrank ℝ F = finrank ℝ (EuclideanSpace ℝ (Fin 3)) + 1 := by simp [hF]
  have hcard :=
    natCard_connectedComponents_sphere_compl_range_eq_two hEF hf_lf.continuous hf_lf.injective
  have hne : Nonempty (ConnectedComponents ↥(range f)ᶜ) :=
    (Nat.card_pos_iff.1 (by rw [hcard]; positivity)).1
  obtain ⟨⟨y, hy⟩, -⟩ := Quotient.exists_rep hne.some
  obtain ⟨g, hg_cl, -, hgf⟩ := hf_lf.exists_isClosedEmbedding_closedBall_sphere hEG hEF hy
  exact ⟨g, hg_cl, hgf⟩

/-- **Alexander's theorem** for the standard 3-sphere `S³ ⊂ ℝ⁴`: every closed locally flat embedded
2-sphere bounds a closed embedded 3-ball. -/
theorem isSphereBoundsBall_sphere_euclideanSpace_fin_four :
    IsSphereBoundsBall (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  isSphereBoundsBall_sphere (by simp)

/-- `TopCat.sphere 3` satisfies `IsSphereBoundsBall` in every universe. -/
theorem isSphereBoundsBall_topCatSphere_three : IsSphereBoundsBall (TopCat.sphere.{u} 3) :=
  Homeomorph.ulift.symm.isSphereBoundsBall_iff.1 isSphereBoundsBall_sphere_euclideanSpace_fin_four

/-- `EuclideanSpace ℝ (Fin 3)` satisfies `IsSphereBoundsBall`: every closed locally flat embedded
2-sphere in `ℝ³` bounds a closed embedded 3-ball. -/
theorem isSphereBoundsBall_euclideanSpace_fin_three :
    IsSphereBoundsBall (EuclideanSpace ℝ (Fin 3)) := by
  rw [isSphereBoundsBall_iff_sphere_closedBall]
  intro f _ hf_lf
  obtain ⟨g, hg_cl, -, hgf⟩ := hf_lf.exists_isClosedEmbedding_closedBall (by simp)
  exact ⟨g, hg_cl, hgf⟩

/-- Every 3-dimensional real normed space satisfies `IsSphereBoundsBall`. -/
theorem isSphereBoundsBall_of_finrank_eq_three {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : finrank ℝ E = 3) : IsSphereBoundsBall E := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := ContinuousLinearEquiv.ofFinrankEq (by simp [hE])
  exact L.toHomeomorph.symm.isSphereBoundsBall_iff.1 isSphereBoundsBall_euclideanSpace_fin_three

/-! ### Reducibility of sphere products and punctured 3-space -/

/-- If `X` is a `T₁` space admitting an open embedding `ι : ℝ → X` and `dim E = 3`, then
`X × sphere (0 : E) 1` does not satisfy `IsSphereBoundsBall`. -/
theorem not_isSphereBoundsBall_prod_sphere_of_isOpenEmbedding
    {X : Type u} [TopologicalSpace X] [T1Space X] {ι : ℝ → X} (hι : IsOpenEmbedding ι)
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 3) :
    ¬ IsSphereBoundsBall (X × sphere (0 : E) 1) := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  let eS : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ sphere (0 : E) 1 :=
    sphereHomeomorphOfFinrankEq (by simp [hE])
  let f : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → X × sphere (0 : E) 1 := fun y ↦ (ι 0, eS y)
  let b : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ → X × sphere (0 : E) 1 :=
    Prod.map ι eS ∘ Homeomorph.prodComm _ _
  have hb : IsBicollar f b :=
    ⟨(hι.prodMap eS.isOpenEmbedding).comp (Homeomorph.prodComm _ _).isOpenEmbedding, fun _ ↦ rfl⟩
  have hf_lf : IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f := hb.isLocallyFlat
  have hrng : range f = {ι 0} ×ˢ univ := by
    ext ⟨x, y⟩
    simp only [f, mem_range, Prod.mk.injEq, mem_prod, mem_singleton_iff, mem_univ, and_true]
    exact ⟨fun ⟨_, hx, _⟩ ↦ hx.symm, fun hx ↦ ⟨eS.symm y, hx.symm, eS.apply_symm_apply y⟩⟩
  have hf_cl : IsClosedEmbedding f :=
    ⟨hf_lf.isEmbedding, hrng ▸ isClosed_singleton.prod isClosed_univ⟩
  exact not_isSphereBoundsBall_of_leftInverse (E := EuclideanSpace ℝ (Fin 3)) (by simp) hf_cl hf_lf
    (r := fun q ↦ eS.symm q.2) (eS.symm.continuous.comp continuous_snd)
    fun y ↦ eS.symm_apply_apply y

/-- For any nonempty `T₁` space `X` charted on a 1-dimensional real normed space `H` and any
3-dimensional real normed space `E`, the product `X × sphere (0 : E) 1` does not satisfy
`IsSphereBoundsBall`. -/
theorem not_isSphereBoundsBall_prod_sphere
    {X : Type u} [TopologicalSpace X] [T1Space X] [Nonempty X]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ChartedSpace H X]
    (hH : finrank ℝ H = 1)
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 3) :
    ¬ IsSphereBoundsBall (X × sphere (0 : E) 1) := by
  have : FiniteDimensional ℝ H := .of_finrank_pos (by omega)
  let L : ℝ ≃L[ℝ] H := ContinuousLinearEquiv.ofFinrankEq (by simp [hH])
  obtain ⟨x₀⟩ := ‹Nonempty X›
  let φ := chartAt H x₀
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.1 φ.open_target (φ x₀) (φ.map_source (mem_chart_source H x₀))
  let ρ := OpenPartialHomeomorph.univBall (φ x₀) r
  have hρ : IsOpenEmbedding (ρ ∘ L) :=
    (ρ.isOpenEmbedding (OpenPartialHomeomorph.univBall_source _ _)).comp
      L.toHomeomorph.isOpenEmbedding
  have hrng : range (ρ ∘ L) ⊆ φ.symm.source := by
    rintro _ ⟨t, rfl⟩
    rw [φ.symm_source]
    have ht : L t ∈ ρ.source := by simp [ρ]
    exact hball (OpenPartialHomeomorph.univBall_target (φ x₀) hr ▸ ρ.map_source ht)
  exact not_isSphereBoundsBall_prod_sphere_of_isOpenEmbedding
    (φ.symm.isOpenEmbedding_comp hρ hrng) hE

/-- **`S¹ × S²` is reducible**: `Circle × sphere (0 : E) 1` does not satisfy `IsSphereBoundsBall`
when `dim E = 3`. -/
theorem not_isSphereBoundsBall_circle_prod_sphere
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 3) :
    ¬ IsSphereBoundsBall (Circle × sphere (0 : E) 1) :=
  not_isSphereBoundsBall_prod_sphere (H := EuclideanSpace ℝ (Fin 1)) (by simp) hE

/-- **Punctured 3-space is reducible**: `E \ {p}` does not satisfy `IsSphereBoundsBall` when
`dim E = 3`. -/
theorem not_isSphereBoundsBall_compl_singleton
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 3) (p : E) :
    ¬ IsSphereBoundsBall ({p}ᶜ : Set E) := by
  let _ : ChartedSpace ℝ (Ioi (0 : ℝ)) :=
    TopologicalSpace.Opens.instChartedSpace ⟨Ioi 0, isOpen_Ioi⟩
  have : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, one_pos⟩⟩
  let e₁ : ({p}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E) :=
    (Homeomorph.subRight p).subtype fun x ↦ by simp [sub_eq_zero]
  let e : ({p}ᶜ : Set E) ≃ₜ Ioi (0 : ℝ) × sphere (0 : E) 1 :=
    e₁.trans ((homeomorphUnitSphereProd E).trans (Homeomorph.prodComm _ _))
  exact mt e.isSphereBoundsBall_iff.1
    (not_isSphereBoundsBall_prod_sphere (H := ℝ) (finrank_self ℝ) hE)

end TauCeti
