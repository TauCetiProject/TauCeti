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

* `TauCeti.SmoothCollar`: a `C^k` smooth collar of a manifold modeled on `EuclideanHalfSpace`.
* `TauCeti.SmoothCollar.opensRange`: its image, an open neighbourhood of the boundary.
* `TauCeti.SmoothCollar.reparam`: the collar precomposed with `id × ψ` for a diffeomorphism `ψ`
  of `[0, 1)` fixing `0`.
* `TauCeti.SmoothCollar.ofIsEmpty`: the empty collar of a manifold with empty boundary.

## Main results

* `TauCeti.SmoothCollar.isOpenEmbedding`: a smooth collar is an open embedding.
* `TauCeti.SmoothCollar.boundary_subset_range`: its image contains the boundary.
* `TauCeti.SmoothCollar.isCollar`: a smooth collar is a topological collar of the boundary
  inclusion.

The local smooth collars, defined near single boundary points, are
`TauCeti.IsProductCollarChart.diffeomorphProd`.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, Theorem 6.1.
* J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 9.25.
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti

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
  apply_zero' : ∀ x, toFun (x, normalIioOpensZero one_pos) = x

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

/-- The coercion of a smooth collar built from its fields is the underlying map. -/
@[simp]
theorem coe_mk (f : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1 → M)
    (h₁ : IsLocalDiffeomorph ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k f) (h₂ : Injective f)
    (h₃ : ∀ x, f (x, normalIioOpensZero one_pos) = x) :
    ⇑(⟨f, h₁, h₂, h₃⟩ : SmoothCollar n k M) = f := rfl

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
theorem apply_zero (x : ↥((𝓡∂ (n + 1)).boundary M)) : c (x, normalIioOpensZero one_pos) = x :=
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
  ⟨(⟨x, hx⟩, normalIioOpensZero one_pos), c.apply_zero _⟩

/-- The image of a smooth collar, an open neighbourhood of the boundary. -/
def opensRange : TopologicalSpace.Opens M := ⟨range c, c.isOpen_range⟩

/-- The image of a smooth collar is the range of its underlying map. -/
@[simp]
theorem coe_opensRange : (c.opensRange : Set M) = range c := (rfl)

/-- The image of a smooth collar is a neighbourhood of the boundary. -/
theorem opensRange_mem_nhdsSet : (c.opensRange : Set M) ∈ 𝓝ˢ ((𝓡∂ (n + 1)).boundary M) :=
  c.isOpen_range.mem_nhdsSet.2 c.boundary_subset_range

/-- A point of `∂M × [0, 1)` is sent to the boundary exactly when its depth is zero. -/
theorem apply_mem_boundary_iff (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1) :
    c p ∈ (𝓡∂ (n + 1)).boundary M ↔ p.2 = normalIioOpensZero one_pos := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact congrArg Prod.snd (c.injective (c.apply_zero ⟨c p, h⟩).symm)
  · obtain ⟨x, t⟩ := p
    obtain rfl : t = normalIioOpensZero one_pos := h
    simp

/-- **A smooth collar is a topological collar** of the boundary inclusion, once its depth
parameter is read as the real interval `[0, 1)` through `homeomorphNormalIioOpens`. -/
theorem isCollar :
    IsCollar (Subtype.val : ↥((𝓡∂ (n + 1)).boundary M) → M)
      (c ∘ Prod.map id (homeomorphNormalIioOpens 1).symm) :=
  ⟨c.isOpenEmbedding.comp
      (IsOpenEmbedding.id.prodMap (homeomorphNormalIioOpens 1).symm.isOpenEmbedding),
    fun x ↦ by
      rw [comp_apply, Prod.map_apply, id, homeomorphNormalIioOpens_symm_zero]
      exact c.apply_zero x⟩

include c in
/-- The boundary inclusion of a manifold with a smooth collar is topologically collared. -/
theorem isCollared : IsCollared (Subtype.val : ↥((𝓡∂ (n + 1)).boundary M) → M) :=
  c.isCollar.isCollared

/-- **Reparametrizing the depth of a collar.** Precomposing a smooth collar with `id × ψ` for a
`C^k` diffeomorphism `ψ` of `[0, 1)` fixing `0` gives a smooth collar. -/
def reparam (ψ : Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (normalIioOpens 1) (normalIioOpens 1) k)
    (hψ : ψ (normalIioOpensZero one_pos) = normalIioOpensZero one_pos) : SmoothCollar n k M where
  toFun := c ∘ Prod.map id ψ
  isLocalDiffeomorph' p := by
    have h :=
      ((Diffeomorph.refl 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) _ k).prodCongr ψ).isLocalDiffeomorph p
    rw [Diffeomorph.coe_prodCongr, Diffeomorph.coe_refl] at h
    exact h.comp _ _ (c.isLocalDiffeomorph _)
  injective' := c.injective.comp (injective_id.prodMap ψ.injective)
  apply_zero' x := by simp [hψ]

/-- The reparametrized collar is the collar precomposed with `id × ψ`. -/
@[simp]
theorem reparam_apply (ψ : Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (normalIioOpens 1) (normalIioOpens 1) k)
    (hψ : ψ (normalIioOpensZero one_pos) = normalIioOpensZero one_pos)
    (p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1) :
    c.reparam ψ hψ p = c (p.1, ψ p.2) := (rfl)

/-- Reparametrizing the depth does not change the image of a collar. -/
@[simp]
theorem opensRange_reparam (ψ : Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (normalIioOpens 1) (normalIioOpens 1) k)
    (hψ : ψ (normalIioOpensZero one_pos) = normalIioOpensZero one_pos) :
    (c.reparam ψ hψ).opensRange = c.opensRange := by
  ext x
  simp only [coe_opensRange, mem_range, reparam_apply, Prod.exists]
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
