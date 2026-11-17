/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SphereBundle.LocallyTrivial

/-!
# Fibres of a unit sphere bundle

For a topological fibre bundle `E → B` whose fibres carry norms, the unit sphere `S(E_b)` of the
fibre over `b : B` embeds into the unit sphere bundle `S(E)` (`TauCeti.sphereBundleFiberIncl`,
`TauCeti.isEmbedding_sphereBundleFiberIncl`), with range the fibre `sphereBundleProj F E ⁻¹' {b}`
over `b` (`TauCeti.range_sphereBundleFiberIncl`). When `B` is `T₁` this is a closed embedding
(`TauCeti.isClosedEmbedding_sphereBundleFiberIncl`), and in general `S(E_b)` is homeomorphic to
that fibre (`TauCeti.sphereBundleFiberHomeomorph`).

For a real vector bundle whose fibre norm is continuous on the total space, the projection
`S(E) → B` is a Serre fibration (`TauCeti.TopCat.mem_serreFibrations_sphereBundleProj`), so over an
`m`-connected base (`π_k(B, b)` trivial for `k ≤ m`) the fibre inclusion `S(E_b) → S(E)` is an
`m`-connected map (`TauCeti.isNConnected_sphereBundleFiberIncl`). This is the connectivity input
comparing a fibre sphere with the total space of a sphere bundle over a highly connected base in
Barraud–Damian–Humilière–Oancea, Proposition 6.23.

## Main declarations

* `TauCeti.sphereBundleFiberIncl`: the continuous inclusion `S(E_b) → S(E)`.
* `TauCeti.isEmbedding_sphereBundleFiberIncl`, `TauCeti.isClosedEmbedding_sphereBundleFiberIncl`,
  `TauCeti.range_sphereBundleFiberIncl`: topological embedding properties and range.
* `TauCeti.sphereBundleFiberHomeomorph`: `S(E_b) ≃ₜ sphereBundleProj F E ⁻¹' {b}`.
* `TauCeti.isNConnected_sphereBundleFiberIncl`: `S(E_b) → S(E)` is `m`-connected over an
  `m`-connected base.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§12.1–12.2 and
  §17.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.23.
-/

public section

noncomputable section

open Bundle Metric Set Topology
open scoped Topology.Homotopy

universe w

namespace TauCeti

section Fiber

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E]

/-- The inclusion `S(E_b) → S(E)` of the unit sphere of the fibre over `b` into the unit sphere
bundle. -/
def sphereBundleFiberIncl (b : B) : C(sphere (0 : E b) 1, sphereBundle F E) where
  toFun p := ⟨⟨b, (p : E b)⟩, mem_sphereBundle.2 (norm_eq_of_mem_sphere p)⟩
  continuous_toFun :=
    ((FiberBundle.continuous_totalSpaceMk F E b).comp continuous_subtype_val).subtype_mk _

variable {F E}

@[simp]
theorem coe_sphereBundleFiberIncl_apply (b : B) (p : sphere (0 : E b) 1) :
    (sphereBundleFiberIncl F E b p : TotalSpace F E) = ⟨b, (p : E b)⟩ :=
  (rfl)

@[simp]
theorem sphereBundleFiberIncl_unitSphereOfSphereBundle (q : sphereBundle F E) :
    sphereBundleFiberIncl F E q.1.proj (unitSphereOfSphereBundle q) = q :=
  Subtype.ext (by simp)

theorem sphereBundleProj_sphereBundleFiberIncl (b : B) (p : sphere (0 : E b) 1) :
    sphereBundleProj F E (sphereBundleFiberIncl F E b p) = b :=
  sphereBundleProj_apply F E _

@[simp]
theorem sphereBundleProj_comp_sphereBundleFiberIncl (b : B) :
    (sphereBundleProj F E).comp (sphereBundleFiberIncl F E b) = ContinuousMap.const _ b := by
  ext p
  simp

variable (F E)

/-- The inclusion `S(E_b) → S(E)` is a topological embedding. -/
theorem isEmbedding_sphereBundleFiberIncl (b : B) :
    IsEmbedding (sphereBundleFiberIncl F E b) :=
  IsEmbedding.subtypeVal.of_comp_iff.1
    ((FiberBundle.totalSpaceMk_isEmbedding F E b).comp IsEmbedding.subtypeVal)

/-- The inclusion `S(E_b) → S(E)` is injective. -/
theorem sphereBundleFiberIncl_injective (b : B) :
    Function.Injective (sphereBundleFiberIncl F E b) :=
  (isEmbedding_sphereBundleFiberIncl F E b).injective

/-- The range of `S(E_b) → S(E)` is the fibre of `S(E) → B` over `b`. -/
theorem range_sphereBundleFiberIncl (b : B) :
    range (sphereBundleFiberIncl F E b) = sphereBundleProj F E ⁻¹' {b} := by
  refine Subset.antisymm (range_subset_iff.2 fun p ↦ by simp) fun q hq ↦ ?_
  obtain ⟨⟨b', v⟩, hv⟩ := q
  obtain rfl : b' = b := by simpa using hq
  exact ⟨⟨v, mem_sphere_zero_iff_norm.2 (mem_sphereBundle.1 hv)⟩, rfl⟩

/-- When the base is `T₁`, the inclusion `S(E_b) → S(E)` is a closed embedding. -/
theorem isClosedEmbedding_sphereBundleFiberIncl [T1Space B] (b : B) :
    IsClosedEmbedding (sphereBundleFiberIncl F E b) where
  toIsEmbedding := isEmbedding_sphereBundleFiberIncl F E b
  isClosed_range := by
    rw [range_sphereBundleFiberIncl]
    exact isClosed_singleton.preimage (sphereBundleProj F E).continuous

/-- **Homeomorphism onto a fibre of the sphere bundle.** The unit sphere `S(E_b)` is homeomorphic
to the fibre of `S(E) → B` over `b`. -/
def sphereBundleFiberHomeomorph (b : B) :
    sphere (0 : E b) 1 ≃ₜ sphereBundleProj F E ⁻¹' {b} :=
  (isEmbedding_sphereBundleFiberIncl F E b).toHomeomorph.trans
    (Homeomorph.setCongr (range_sphereBundleFiberIncl F E b))

variable {F E}

@[simp]
theorem coe_sphereBundleFiberHomeomorph_apply (b : B) (p : sphere (0 : E b) 1) :
    (sphereBundleFiberHomeomorph F E b p : sphereBundle F E) = sphereBundleFiberIncl F E b p :=
  (rfl)

@[simp]
theorem sphereBundleFiberIncl_sphereBundleFiberHomeomorph_symm (b : B)
    (q : sphereBundleProj F E ⁻¹' {b}) :
    sphereBundleFiberIncl F E b ((sphereBundleFiberHomeomorph F E b).symm q) = q :=
  congrArg Subtype.val ((sphereBundleFiberHomeomorph F E b).apply_symm_apply q)

end Fiber

end TauCeti

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, NormedSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- Over its base set, the induced sphere-bundle chart reads a point of the fibre sphere `S(E_b)`
by normalizing its coordinates in `e`. -/
theorem coe_sphereBundle_sphereBundleFiberIncl (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) {b : B} (hb : b ∈ e.baseSet)
    (p : sphere (0 : E b) 1) :
    ((e.sphereBundle hnorm (sphereBundleFiberIncl F E b p)).2 : F) =
      NormedSpace.normalize (e ⟨b, (p : E b)⟩).2 :=
  e.coe_sphereBundle_apply_snd hnorm hb

end Bundle.Trivialization

namespace TauCeti

section LocallyTrivial

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, NormedSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **Connectivity of the sphere-fibre inclusion over a highly connected base.** If the fibre norm
is continuous on the total space and `π_k(B, b)` is trivial for every `k ≤ m`, then the fibre
inclusion `S(E_b) → S(E)` is an `m`-connected map: it induces bijections on `π_k` for `k < m` and a
surjection on `π_m`. -/
theorem isNConnected_sphereBundleFiberIncl (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    {b : B} {m : ℕ} (hB : ∀ k ≤ m, Subsingleton (π_ k B b)) :
    (sphereBundleFiberIncl F E b).IsNConnected m := by
  let p : _root_.TopCat.of (sphereBundle F E) ⟶ _root_.TopCat.of B :=
    _root_.TopCat.ofHom (sphereBundleProj F E)
  have hfib : (p.fiberι b).hom.IsNConnected m :=
    TopCat.isNConnected_fiberι_of_mem_serreFibrations
      (TopCat.mem_serreFibrations_sphereBundleProj F E hnorm) hB
  let φ : sphere (0 : E b) 1 ≃ₜ p.fiber b :=
    (sphereBundleFiberHomeomorph F E b).trans ((Homeomorph.refl _).subtype fun _ ↦ Iff.rfl)
  convert hfib.comp (φ.toHomotopyEquiv.isWeakHomotopyEquivalence.isNConnected m) using 1
  ext x : 1
  exact (TopCat.Hom.fiberι_apply p b (φ x)).symm

end LocallyTrivial

end TauCeti
