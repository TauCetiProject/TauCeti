/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Topology.Algebra.Module.ProdUnitsHomeomorph
public import TauCeti.Topology.Compactification.OnePoint.Collapse
public import TauCeti.Topology.Compactification.OnePoint.Sphere

/-!
# The Pontryagin–Thom collapse of a framed tube

Let `f : S → M` be the inclusion of a compact submanifold `S` of codimension `k` whose normal
bundle is framed, that is, trivialized as `S × ℝᵏ`. A tubular neighbourhood of `S` identifies the
framed normal bundle with an open neighbourhood of `S`, through an open embedding
`τ : S × ℝᵏ → M` with `τ (x, 0) = f x`; this is a **framed tube** around `f`
(`TauCeti.IsFramedTube`). The **Pontryagin–Thom collapse** of `τ` is the map
`c : M → OnePoint ℝᵏ ≅ Sᵏ` sending `τ (x, v)` to `v` and every point outside the tube to `∞`
(`TauCeti.pontryaginThomCollapse`). It is continuous when `S` is compact and `M` is Hausdorff
(`TauCeti.continuous_pontryaginThomCollapse`), and the submanifold is the preimage of the origin
(`TauCeti.IsFramedTube.pontryaginThomCollapse_eq_zero_iff`). Only the topology of the tube is
used; the ambient space `M` is an arbitrary Hausdorff space, for instance a closed manifold, and
the fibre `V` an arbitrary topological space with a zero.

The collapse is unchanged up to homotopy under isotopy of the tube and homotopy of the framing:

* a continuous family of tubes `τ t`, `t ∈ [0, 1]`, whose total map
  `(t, x, v) ↦ (t, τ t (x, v))` is an open embedding, gives a homotopy between the collapses of
  `τ 0` and `τ 1` (`TauCeti.pontryaginThomCollapseMap_homotopic`);
* in particular, changing the framing by a continuous family `A : S → GL(V)` of linear
  automorphisms of a normed space `V` (`TauCeti.prodUnitsHomeomorph`) keeps `τ` a framed tube
  (`TauCeti.IsFramedTube.comp_prodUnitsHomeomorph`), and homotopic changes of framing give
  homotopic collapses (`TauCeti.pontryaginThomCollapseMap_comp_prodUnitsHomeomorph_homotopic`).

For `V = ℝᵏ`, composing with a homeomorphism `OnePoint ℝᵏ ≃ₜ Sᵏ` sending `∞` to a basepoint `s₀`
gives the collapse onto the sphere, `TauCeti.pontryaginThomSphereMap`, which sends the complement
of the tube to `s₀`.

## Main declarations

* `TauCeti.IsFramedTube f τ`: `τ : S × V → M` is an open embedding extending `f` along the zero
  section.
* `TauCeti.pontryaginThomCollapse τ`: the Pontryagin–Thom collapse `M → OnePoint V`.
* `TauCeti.pontryaginThomCollapseMap`: the collapse as a continuous map.
* `TauCeti.pontryaginThomCollapseMap_homotopic`: isotopic tubes have homotopic collapses.
* `TauCeti.pontryaginThomSphereMap`: the collapse onto the sphere `Sᵏ`.

## References

* L. S. Pontryagin, *Smooth manifolds and their applications in homotopy theory*, Amer. Math.
  Soc. Transl. (2) 11 (1959), 1–114.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia,
  1965, §7.
-/

public section

open Function Set Topology OnePoint

namespace TauCeti

variable {S M V : Type*}

section Collapse

/-- A **framed tube** around `f : S → M` with fibre `V` is an open embedding `τ : S × V → M` that
restricts to `f` on the zero section. For a submanifold `S` of `M` with a framing of its normal
bundle, a tubular neighbourhood composed with the framing is a framed tube with fibre `ℝᵏ`. -/
structure IsFramedTube [TopologicalSpace S] [TopologicalSpace M] [TopologicalSpace V] [Zero V]
    (f : S → M) (τ : S × V → M) : Prop where
  /-- The tube is an open embedding. -/
  isOpenEmbedding : IsOpenEmbedding τ
  /-- The tube restricts to `f` on the zero section. -/
  apply_zero : ∀ x, τ (x, 0) = f x

/-- The **Pontryagin–Thom collapse** of a tube `τ : S × V → M`: the point `τ (x, v)` goes to `v`,
and every point outside the tube goes to `∞`. It is continuous when `τ` is an open embedding, `S`
is compact and `M` is Hausdorff (`TauCeti.continuous_pontryaginThomCollapse`). -/
noncomputable def pontryaginThomCollapse (τ : S × V → M) : M → OnePoint V :=
  onePointCollapse τ Prod.snd

variable {τ : S × V → M}

@[simp]
theorem pontryaginThomCollapse_apply (hτ : Injective τ) (x : S) (v : V) :
    pontryaginThomCollapse τ (τ (x, v)) = v :=
  onePointCollapse_apply hτ _ (x, v)

@[simp]
theorem pontryaginThomCollapse_of_notMem_range {m : M} (hm : m ∉ range τ) :
    pontryaginThomCollapse τ m = ∞ :=
  onePointCollapse_of_notMem_range hm

/-- The collapse sends exactly the points outside the tube to `∞`. -/
theorem pontryaginThomCollapse_eq_infty_iff (hτ : Injective τ) {m : M} :
    pontryaginThomCollapse τ m = ∞ ↔ m ∉ range τ :=
  onePointCollapse_eq_infty_iff hτ

/-- The fibre of the collapse over a point `v` of `V` is the parallel copy `τ (S × {v})`. -/
theorem pontryaginThomCollapse_eq_coe_iff (hτ : Injective τ) {m : M} {v : V} :
    pontryaginThomCollapse τ m = v ↔ ∃ x, τ (x, v) = m := by
  rw [pontryaginThomCollapse, onePointCollapse_eq_coe_iff hτ]
  exact ⟨fun ⟨⟨x, w⟩, hw, hm⟩ ↦ ⟨x, hw ▸ hm⟩, fun ⟨x, hm⟩ ↦ ⟨(x, v), rfl, hm⟩⟩

namespace IsFramedTube

variable [TopologicalSpace S] [TopologicalSpace M] [TopologicalSpace V] [Zero V] {f : S → M}

/-- The collapse sends the core of a framed tube to the origin. -/
@[simp]
theorem pontryaginThomCollapse_apply_self (h : IsFramedTube f τ) (x : S) :
    pontryaginThomCollapse τ (f x) = (0 : V) := by
  rw [← h.apply_zero, pontryaginThomCollapse_apply h.isOpenEmbedding.injective]

/-- **The core is the preimage of the origin.** A point of `M` is collapsed to the origin exactly
when it lies on the core of the framed tube. -/
theorem pontryaginThomCollapse_eq_zero_iff (h : IsFramedTube f τ) {m : M} :
    pontryaginThomCollapse τ m = (0 : V) ↔ m ∈ range f := by
  simp [pontryaginThomCollapse_eq_coe_iff h.isOpenEmbedding.injective, h.apply_zero, mem_range]

end IsFramedTube

variable [TopologicalSpace S] [TopologicalSpace M] [TopologicalSpace V]

/-- The Pontryagin–Thom collapse of an open embedding `τ : S × V → M` with compact `S` into a
Hausdorff space is continuous. -/
theorem continuous_pontryaginThomCollapse [CompactSpace S] [T2Space M]
    (hτ : IsOpenEmbedding τ) : Continuous (pontryaginThomCollapse τ) :=
  continuous_onePointCollapse hτ isProperMap_snd_of_compactSpace

/-- The Pontryagin–Thom collapse `M → OnePoint V` of an open embedding `τ : S × V → M` with compact
`S` into a Hausdorff space, as a continuous map. -/
noncomputable def pontryaginThomCollapseMap [CompactSpace S] [T2Space M]
    (hτ : IsOpenEmbedding τ) : C(M, OnePoint V) :=
  ⟨pontryaginThomCollapse τ, continuous_pontryaginThomCollapse hτ⟩

@[simp]
theorem coe_pontryaginThomCollapseMap [CompactSpace S] [T2Space M] (hτ : IsOpenEmbedding τ) :
    ⇑(pontryaginThomCollapseMap hτ) = pontryaginThomCollapse τ :=
  (rfl)

/-- **Isotopic tubes have homotopic collapses.** Let `τ : [0, 1] × (S × V) → M` be a family of
tubes whose total map `(t, p) ↦ (t, τ (t, p))` is an open embedding, with compact `S` and
Hausdorff `M`. Then the Pontryagin–Thom collapses of its ends `τ₀ = τ (0, ·)` and
`τ₁ = τ (1, ·)` are homotopic. -/
theorem pontryaginThomCollapseMap_homotopic [CompactSpace S] [T2Space M] {τ₀ τ₁ : S × V → M}
    (h₀ : IsOpenEmbedding τ₀) (h₁ : IsOpenEmbedding τ₁) {τ : unitInterval × (S × V) → M}
    (hτ : IsOpenEmbedding fun q : unitInterval × (S × V) ↦ (q.1, τ q))
    (hτ₀ : ∀ p, τ (0, p) = τ₀ p) (hτ₁ : ∀ p, τ (1, p) = τ₁ p) :
    (pontryaginThomCollapseMap h₀).Homotopic (pontryaginThomCollapseMap h₁) := by
  refine ⟨{ toFun := fun p ↦ pontryaginThomCollapse (fun q ↦ τ (p.1, q)) p.2
            continuous_toFun := by
              unfold pontryaginThomCollapse
              exact continuous_onePointCollapse_slice (g := fun q ↦ q.2.2) hτ
                (isProperMap_snd_of_compactSpace.comp
                  (isProperMap_snd_of_compactSpace (X := unitInterval)))
            map_zero_left := fun m ↦ ?_
            map_one_left := fun m ↦ ?_ }⟩
  · simp only [coe_pontryaginThomCollapseMap]
    congr 1
    exact funext hτ₀
  · simp only [coe_pontryaginThomCollapseMap]
    congr 1
    exact funext hτ₁

end Collapse

section Framing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace S] [TopologicalSpace M] {f : S → M} {τ : S × V → M}

/-- Changing the framing of a framed tube by a continuous family of linear automorphisms gives a
framed tube around the same core. -/
theorem IsFramedTube.comp_prodUnitsHomeomorph (h : IsFramedTube f τ) {A : S → (V →L[𝕜] V)ˣ}
    (hA : Continuous A) : IsFramedTube f (τ ∘ prodUnitsHomeomorph A hA) where
  isOpenEmbedding := h.isOpenEmbedding.comp (prodUnitsHomeomorph A hA).isOpenEmbedding
  apply_zero x := by simp [h.apply_zero]

omit [TopologicalSpace M] in
/-- The collapse of the reframed tube `(x, v) ↦ τ (x, A x v)` sends `τ (x, v)` to `(A x)⁻¹ v`. -/
theorem pontryaginThomCollapse_comp_prodUnitsHomeomorph_apply (hτ : Injective τ)
    {A : S → (V →L[𝕜] V)ˣ} (hA : Continuous A) (x : S) (v : V) :
    pontryaginThomCollapse (τ ∘ prodUnitsHomeomorph A hA) (τ (x, v)) =
      ((↑(A x)⁻¹ : V →L[𝕜] V) v : V) := by
  have h := pontryaginThomCollapse_apply (hτ.comp (prodUnitsHomeomorph A hA).injective) x
    ((↑(A x)⁻¹ : V →L[𝕜] V) v)
  simpa [← mul_apply_eq_comp] using h

/-- **Homotopic framings give homotopic collapses.** For a continuous family
`A : [0, 1] × S → GL(V)` of linear automorphisms, the Pontryagin–Thom collapses of the tubes
`(x, v) ↦ τ (x, A (0, x) v)` and `(x, v) ↦ τ (x, A (1, x) v)` are homotopic. -/
theorem pontryaginThomCollapseMap_comp_prodUnitsHomeomorph_homotopic [CompactSpace S] [T2Space M]
    (hτ : IsOpenEmbedding τ) {A : unitInterval × S → (V →L[𝕜] V)ˣ} (hA : Continuous A) :
    (pontryaginThomCollapseMap (hτ.comp (prodUnitsHomeomorph (fun x ↦ A (0, x))
        (hA.comp (Continuous.prodMk_right 0))).isOpenEmbedding)).Homotopic
      (pontryaginThomCollapseMap (hτ.comp (prodUnitsHomeomorph (fun x ↦ A (1, x))
        (hA.comp (Continuous.prodMk_right 1))).isOpenEmbedding)) := by
  -- The total map of the family of reframed tubes is `id × τ` after a homeomorphism of
  -- `[0, 1] × (S × V)` that applies `A` fibrewise.
  let Φ : unitInterval × (S × V) ≃ₜ unitInterval × (S × V) :=
    ((Homeomorph.prodAssoc unitInterval S V).symm.trans (prodUnitsHomeomorph A hA)).trans
      (Homeomorph.prodAssoc unitInterval S V)
  refine pontryaginThomCollapseMap_homotopic _ _
    (τ := fun q ↦ τ (q.2.1, (A (q.1, q.2.1) : V →L[𝕜] V) q.2.2)) ?_ (fun _ ↦ by simp)
    fun _ ↦ by simp
  convert (IsOpenEmbedding.id.prodMap hτ).comp Φ.isOpenEmbedding using 1
  -- `Homeomorph.prodAssoc` has no `apply` simp lemmas; after the reframing is rewritten, the
  -- reassociations are the identity on underlying triples.
  ext ⟨t, x, v⟩ <;> simp [Φ, Homeomorph.trans_apply] <;> rfl

/-- For `V = ℝᵏ`, the Pontryagin–Thom collapse onto the sphere `Sᵏ ⊆ ℝᵏ⁺¹`: the collapse followed
by a homeomorphism `OnePoint ℝᵏ ≃ₜ Sᵏ` sending `∞` to the basepoint `s₀`. -/
noncomputable def pontryaginThomSphereMap {k : ℕ} [CompactSpace S] [T2Space M]
    {τ : S × (Fin k → ℝ) → M} (hτ : IsOpenEmbedding τ)
    (s₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    C(M, Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
  (onePointHomeomorphSphere k s₀ : C(OnePoint (Fin k → ℝ), _)).comp
    (pontryaginThomCollapseMap hτ)

@[simp]
theorem pontryaginThomSphereMap_apply {k : ℕ} [CompactSpace S] [T2Space M]
    {τ : S × (Fin k → ℝ) → M} (hτ : IsOpenEmbedding τ)
    (s₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) (x : S) (v : Fin k → ℝ) :
    pontryaginThomSphereMap hτ s₀ (τ (x, v)) = onePointHomeomorphSphere k s₀ v := by
  simp [pontryaginThomSphereMap, hτ.injective]

/-- The collapse onto the sphere sends every point outside the tube to the basepoint. -/
@[simp]
theorem pontryaginThomSphereMap_of_notMem_range {k : ℕ} [CompactSpace S] [T2Space M]
    {τ : S × (Fin k → ℝ) → M} (hτ : IsOpenEmbedding τ)
    (s₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) {m : M} (hm : m ∉ range τ) :
    pontryaginThomSphereMap hτ s₀ m = s₀ := by
  simp [pontryaginThomSphereMap, pontryaginThomCollapse_of_notMem_range hm]

/-- Isotopic tubes have homotopic collapses onto the sphere. -/
theorem pontryaginThomSphereMap_homotopic {k : ℕ} [CompactSpace S] [T2Space M]
    {τ₀ τ₁ : S × (Fin k → ℝ) → M} (h₀ : IsOpenEmbedding τ₀) (h₁ : IsOpenEmbedding τ₁)
    {τ : unitInterval × (S × (Fin k → ℝ)) → M}
    (hτ : IsOpenEmbedding fun q : unitInterval × (S × (Fin k → ℝ)) ↦ (q.1, τ q))
    (hτ₀ : ∀ p, τ (0, p) = τ₀ p) (hτ₁ : ∀ p, τ (1, p) = τ₁ p)
    (s₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    (pontryaginThomSphereMap h₀ s₀).Homotopic (pontryaginThomSphereMap h₁ s₀) :=
  (ContinuousMap.Homotopic.refl _).comp (pontryaginThomCollapseMap_homotopic h₀ h₁ hτ hτ₀ hτ₁)

end Framing

end TauCeti
