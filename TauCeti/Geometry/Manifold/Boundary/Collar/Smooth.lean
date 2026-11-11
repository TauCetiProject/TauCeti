/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Boundary.Collar.Global
public import TauCeti.Geometry.Manifold.Boundary.Collar.Local

/-!
# Smooth collars of a manifold with boundary

A smooth collar of a manifold with boundary `M` is a smooth embedding `c : ∂M × [0, 1) → M`
with open image whose restriction to `∂M × {0}` is the inclusion of the boundary. Here `∂M`
carries the canonical manifold structure `TauCeti.boundaryChartedSpace`, modeled on
`EuclideanSpace ℝ (Fin n)`, and the depth parameter `[0, 1)` is the open subspace
`TauCeti.EuclideanHalfSpace.normalIioOpens 1` of the one-dimensional half-space model, so
`∂M × [0, 1)` is a manifold over `(𝓡 n).prod (𝓡∂ 1)`.

Since source and target have the same dimension, a smooth embedding with open image is the same
as an injective local diffeomorphism, and this is how the structure records it: the fields are
`IsLocalDiffeomorph`, injectivity and the zero-slice equation. Openness of the image and the
open-embedding property are consequences (`TauCeti.SmoothCollar.isOpen_range`,
`TauCeti.SmoothCollar.isOpenEmbedding`).

A collar is data: gluing along the boundary takes its collars as arguments. A smooth collar
forgets to the topological predicate `TauCeti.IsCollar` once its depth parameter is read as the
real interval `[0, 1)` (`TauCeti.SmoothCollar.isCollar`).

## Main definitions

* `TauCeti.EuclideanHalfSpace.normalIioOpensZero`: the origin of the depth parameter `[0, 1)`.
* `TauCeti.SmoothCollar`: a `C^k` smooth collar of a manifold modeled on `EuclideanHalfSpace`.
* `TauCeti.SmoothCollar.image`: its image, an open neighbourhood of the boundary.
* `TauCeti.SmoothCollar.reparam`: the collar precomposed with `id × ψ` for a diffeomorphism `ψ`
  of `[0, 1)` fixing `0`.
* `TauCeti.SmoothCollar.ofIsEmpty`: the empty collar of a manifold with empty boundary.

## Main results

* `TauCeti.SmoothCollar.isOpenEmbedding`: a smooth collar is an open embedding.
* `TauCeti.SmoothCollar.boundary_subset_range`: its image contains the boundary.
* `TauCeti.SmoothCollar.isCollar`: a smooth collar is a topological collar of the boundary
  inclusion.

## Roadmap

This is the smooth collar structure of Layer 1.1 of the GeometricTopology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`). The existence theorem (Hirsch, *Differential
Topology*, Chapter 4, Theorem 6.1; Lee, *Introduction to Smooth Manifolds*, Theorem 9.25) is not
proved here: the local smooth collars are `TauCeti.IsProductCollarChart.diffeomorphProd`, and
assembling them into one collar of the whole boundary is the remaining step.
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti

namespace EuclideanHalfSpace

/-- The origin of the depth parameter `[0, 1)` of a collar, as a point of the open subspace
`normalIioOpens 1` of the one-dimensional half-space model. -/
@[expose] def normalIioOpensZero : normalIioOpens 1 :=
  ⟨0, mem_normalIioOpens.2 (by simp)⟩

/-- The origin of the depth parameter is the origin of the half-space model. -/
@[simp]
theorem coe_normalIioOpensZero : (normalIioOpensZero : EuclideanHalfSpace 1) = 0 := rfl

/-- The depth parameter `normalIioOpens 1`, read by its normal coordinate as the real interval
`[0, 1)`. This is `homeomorphNormalIio 1`, stated for the open subspace. -/
def homeomorphNormalIioOpens : normalIioOpens 1 ≃ₜ Ico (0 : ℝ) 1 :=
  (Homeomorph.setCongr (Set.ext fun _ ↦ mem_normalIioOpens.trans mem_normalIio.symm)).trans
    (homeomorphNormalIio 1)

/-- The real interval reading of the depth parameter is its normal coordinate. -/
@[simp]
theorem coe_homeomorphNormalIioOpens (t : normalIioOpens 1) :
    (homeomorphNormalIioOpens t : ℝ) = (t : EuclideanHalfSpace 1).1 0 :=
  coe_homeomorphNormalIio _

/-- The origin of the real interval `[0, 1)` corresponds to the origin of the depth parameter. -/
@[simp]
theorem homeomorphNormalIioOpens_symm_zero :
    homeomorphNormalIioOpens.symm 0 = normalIioOpensZero :=
  homeomorphNormalIioOpens.symm_apply_eq.2 <| Subtype.ext (by simp)

end EuclideanHalfSpace

open _root_.TauCeti.EuclideanHalfSpace

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

variable (n k M) in
/-- A `C^k` **smooth collar** of a manifold with boundary `M`, modeled on the Euclidean
half-space: an injective `C^k` local diffeomorphism `c : ∂M × [0, 1) → M` whose zero slice is the
inclusion of the boundary. Equivalently, `c` is a `C^k` embedding with open image; openness is
`SmoothCollar.isOpen_range`.

The boundary carries the canonical manifold structure `boundaryChartedSpace`, and the depth
parameter is the open subspace `normalIioOpens 1` of the one-dimensional half-space model. -/
structure SmoothCollar where
  /-- The underlying map of a smooth collar. Use the coercion to a function instead. -/
  toFun : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1 → M
  isLocalDiffeomorph' : IsLocalDiffeomorph ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k toFun
  injective' : Injective toFun
  apply_zero' : ∀ x, toFun (x, normalIioOpensZero) = x

namespace SmoothCollar

instance : FunLike (SmoothCollar n k M) (↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1) M where
  coe := toFun
  coe_injective c d h := by
    cases c
    cases d
    congr

/-- The structure field `toFun` is the coercion to a function. -/
@[simp]
theorem toFun_eq_coe (c : SmoothCollar n k M) : c.toFun = ⇑c := rfl

/-- Two smooth collars with the same underlying map are equal. -/
@[ext]
theorem ext {c d : SmoothCollar n k M} (h : ∀ p, c p = d p) : c = d := DFunLike.ext _ _ h

variable (c : SmoothCollar n k M)

/-- A smooth collar is a `C^k` local diffeomorphism. -/
protected theorem isLocalDiffeomorph :
    IsLocalDiffeomorph ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k c :=
  c.isLocalDiffeomorph'

/-- A smooth collar is injective. -/
protected theorem injective : Injective c := c.injective'

/-- The zero slice of a smooth collar is the inclusion of the boundary. -/
@[simp]
theorem apply_zero (x : ↥((𝓡∂ (n + 1)).boundary M)) : c (x, normalIioOpensZero) = x :=
  c.apply_zero' x

/-- A smooth collar is `C^k`. -/
protected theorem contMDiff : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k c :=
  c.isLocalDiffeomorph.contMDiff

/-- A smooth collar is continuous. -/
protected theorem continuous : Continuous c := c.isLocalDiffeomorph.isLocalHomeomorph.continuous

/-- A smooth collar is an open embedding. -/
theorem isOpenEmbedding : IsOpenEmbedding c :=
  c.isLocalDiffeomorph.isLocalHomeomorph.isOpenEmbedding_of_injective c.injective

/-- The image of a smooth collar is open. -/
theorem isOpen_range : IsOpen (range c) := c.isLocalDiffeomorph.isOpen_range

/-- The image of a smooth collar contains the boundary. -/
theorem boundary_subset_range : (𝓡∂ (n + 1)).boundary M ⊆ range c := fun x hx ↦
  ⟨(⟨x, hx⟩, normalIioOpensZero), c.apply_zero _⟩

/-- The image of a smooth collar, an open neighbourhood of the boundary. -/
@[expose] def image : TopologicalSpace.Opens M := ⟨range c, c.isOpen_range⟩

/-- The image of a smooth collar is the range of its underlying map. -/
@[simp]
theorem coe_image : (c.image : Set M) = range c := rfl

/-- The image of a smooth collar is a neighbourhood of the boundary. -/
theorem image_mem_nhdsSet : (c.image : Set M) ∈ 𝓝ˢ ((𝓡∂ (n + 1)).boundary M) :=
  c.isOpen_range.mem_nhdsSet.2 c.boundary_subset_range

/-- A point of `∂M × [0, 1)` is sent to the boundary exactly when its depth is zero. -/
theorem apply_mem_boundary_iff (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1) :
    c p ∈ (𝓡∂ (n + 1)).boundary M ↔ p.2 = normalIioOpensZero := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := c.injective (c.apply_zero ⟨c p, h⟩).symm
    rw [this]
  · obtain ⟨x, t⟩ := p
    obtain rfl : t = normalIioOpensZero := h
    simp

/-- **A smooth collar is a topological collar** of the boundary inclusion, once its depth
parameter is read as the real interval `[0, 1)` through `homeomorphNormalIioOpens`. -/
theorem isCollar :
    IsCollar (Subtype.val : ↥((𝓡∂ (n + 1)).boundary M) → M)
      (c ∘ Prod.map id homeomorphNormalIioOpens.symm) :=
  ⟨c.isOpenEmbedding.comp
      (IsOpenEmbedding.id.prodMap homeomorphNormalIioOpens.symm.isOpenEmbedding),
    fun x ↦ by simp⟩

include c in
/-- The boundary inclusion of a manifold with a smooth collar is topologically collared. -/
theorem isCollared : IsCollared (Subtype.val : ↥((𝓡∂ (n + 1)).boundary M) → M) :=
  c.isCollar.isCollared

/-- **Reparametrizing the depth of a collar.** Precomposing a smooth collar with `id × ψ` for a
`C^k` diffeomorphism `ψ` of `[0, 1)` fixing `0` gives a smooth collar. -/
@[expose] def reparam (ψ : Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (normalIioOpens 1) (normalIioOpens 1) k)
    (hψ : ψ normalIioOpensZero = normalIioOpensZero) : SmoothCollar n k M where
  toFun := c ∘ Prod.map id ψ
  isLocalDiffeomorph' p := IsLocalDiffeomorphAt.comp
    (hf := ((Diffeomorph.refl 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) _ k).prodCongr ψ).isLocalDiffeomorph p)
    (hg := c.isLocalDiffeomorph _)
  injective' := c.injective.comp (injective_id.prodMap ψ.injective)
  apply_zero' x := by simp [hψ]

/-- The reparametrized collar is the collar precomposed with `id × ψ`. -/
@[simp]
theorem reparam_apply (ψ : Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (normalIioOpens 1) (normalIioOpens 1) k)
    (hψ : ψ normalIioOpensZero = normalIioOpensZero)
    (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1) :
    c.reparam ψ hψ p = c (p.1, ψ p.2) := rfl

/-- Reparametrizing the depth does not change the image of a collar. -/
@[simp]
theorem image_reparam (ψ : Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (normalIioOpens 1) (normalIioOpens 1) k)
    (hψ : ψ normalIioOpensZero = normalIioOpensZero) : (c.reparam ψ hψ).image = c.image := by
  ext x
  simp only [coe_image, mem_range, reparam_apply, Prod.exists]
  refine ⟨fun ⟨a, b, h⟩ ↦ ⟨a, ψ b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨a, ψ.symm b, by simpa using h⟩⟩

section Empty

variable [IsEmpty ((𝓡∂ (n + 1)).boundary M)]

variable (n k M) in
/-- **The empty collar.** A manifold with empty boundary has a smooth collar, the empty map.
The collar existence theorem is vacuous for such manifolds. -/
def ofIsEmpty : SmoothCollar n k M where
  toFun p := isEmptyElim p.1
  isLocalDiffeomorph' p := isEmptyElim p.1
  injective' p := isEmptyElim p.1
  apply_zero' x := isEmptyElim x

/-- A manifold with empty boundary has exactly one smooth collar. -/
instance : Unique (SmoothCollar n k M) where
  default := ofIsEmpty n k M
  uniq _ := ext fun p ↦ isEmptyElim p.1

end Empty

end SmoothCollar

end TauCeti
