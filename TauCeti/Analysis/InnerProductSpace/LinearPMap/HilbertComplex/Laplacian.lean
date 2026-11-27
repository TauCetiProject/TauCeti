/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Normed.Operator.LinearPMap.ProdLp
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.AdjointComp
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Green
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.HilbertComplex.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SubmoduleAdjoint

/-!
# The Laplacian of a Hilbert complex

Let `d₀ : E →ₗ.[𝕜] F` and `d₁ : F →ₗ.[𝕜] G` be densely defined partial linear maps between Hilbert
spaces, with `range d₀ ≤ ker d₁`: one segment of a Hilbert complex, such as the `L²` de Rham
complex or the `L²` realization of an elliptic complex on a closed manifold. Its **Laplacian** at
`F` is

`Δ = d₀ d₀† + d₁† d₁` (`LinearPMap.hodgeLaplacian`),

on its maximal domain, the vectors `u ∈ dom d₀† ∩ dom d₁` with `d₀† u ∈ dom d₀††` and
`d₁ u ∈ dom d₁†`. The first summand is written with the closure `d₀††` of `d₀`, which is `d₀`
itself when `d₀` is closed, as it is in a Hilbert complex. This is the unbounded counterpart of the
bounded Laplacian `ContinuousLinearMap.hodgeLaplacian`.

On `dom d₀† ∩ dom d₁` the Laplacian has the quadratic form
`⟪Δ u, v⟫ = ⟪d₀† u, d₀† v⟫ + ⟪d₁ u, d₁ v⟫` (`LinearPMap.inner_hodgeLaplacian`), so it is
nonnegative and its kernel is the harmonic space `ker d₁ ⊓ ker d₀†`
(`LinearPMap.ker_hodgeLaplacian`).

The main result is that **the Laplacian is self-adjoint** when `d₀` is closable and `d₁` is closed
(`LinearPMap.isSelfAdjoint_hodgeLaplacian`). The proof writes `Δ = T†T` for the closed operator
`T u = (d₀† u, d₁ u)` from `F` to the Hilbert direct sum `E ⊕ G`, on `dom d₀† ∩ dom d₁`, and applies
von Neumann's theorem `LinearPMap.isSelfAdjoint_adjointComp`. The identification of `T†` with
`(a, b) ↦ d₀†† a + d₁† b` on `dom d₀†† × dom d₁†` is where the complex property enters: the
orthogonal projection `P` onto the closed subspace `ker d₁` preserves `dom d₀†` and `d₀†`, since
`(ker d₁)ᗮ ≤ (range d₀)ᗮ = ker d₀†`. Testing `T†` against `P v` and against `v - P v` separates its
two components. The same projection shows that `dom d₀† ∩ dom d₁` is dense.

If moreover the complex has the compactness property `LinearPMap.CompactProperty` at `ε = id`,
that is `dom d₀† ∩ dom d₁` with its graph norm embeds compactly into `F`, the Laplacian has
**compact resolvent** (`LinearPMap.CompactProperty.hasCompactResolvent_hodgeLaplacian`): the
resolvent `(1 + Δ)⁻¹` maps the unit ball into the graph-norm unit ball. Over `ℂ`, the Green
operator `LinearPMap.greenOperator` of the Laplacian then inverts it on the orthogonal complement
of the finite-dimensional harmonic space, and `Δ u = f` is solvable exactly when `f` is orthogonal
to the harmonic space (`LinearPMap.CompactProperty.range_hodgeLaplacian`).

## Main results

* `LinearPMap.hodgeLaplacian`: the Laplacian `d₀ d₀† + d₁† d₁` on its maximal domain, with
  `LinearPMap.mem_hodgeLaplacian_domain` and `LinearPMap.hodgeLaplacian_apply`.
* `LinearPMap.inner_hodgeLaplacian` and `LinearPMap.re_inner_hodgeLaplacian_self`: its quadratic
  form is `‖d₀† u‖² + ‖d₁ u‖²`.
* `LinearPMap.ker_hodgeLaplacian`: its kernel is the harmonic space.
* `LinearPMap.isSelfAdjoint_hodgeLaplacian`: it is self-adjoint.
* `LinearPMap.CompactProperty.hasCompactResolvent_hodgeLaplacian`: the compactness property gives a
  compact resolvent.
* `LinearPMap.CompactProperty.range_hodgeLaplacian`: then its range is the orthogonal complement of
  the harmonic space.

## References

* J. Brüning, M. Lesch, *Hilbert complexes*, J. Funct. Anal. 108 (1992), §2.
* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to
  numerical stability*, Bull. Amer. Math. Soc. 47 (2010), §3.1.
* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968), §7.
-/

public section

noncomputable section

open scoped LinearPMap

namespace LinearPMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### The Laplacian and its quadratic form -/

section Laplacian

variable {d₀ : E →ₗ.[𝕜] F} {d₁ : F →ₗ.[𝕜] G}

variable (d₀ d₁) in
/-- The **Laplacian** `d₀ d₀† + d₁† d₁` of a pair of composable partial linear maps
`d₀ : E →ₗ.[𝕜] F` and `d₁ : F →ₗ.[𝕜] G`, on its maximal domain. The first summand is
`d₀†† d₀†`, which is `d₀ d₀†` when `d₀` is closed and densely defined. -/
def hodgeLaplacian : F →ₗ.[𝕜] F :=
  d₀†.adjointComp + d₁.adjointComp

theorem hodgeLaplacian_def : hodgeLaplacian d₀ d₁ = d₀†.adjointComp + d₁.adjointComp :=
  (rfl)

/-- The domain of the Laplacian consists of the vectors `u ∈ dom d₀† ∩ dom d₁` with
`d₀† u ∈ dom d₀††` and `d₁ u ∈ dom d₁†`. -/
theorem mem_hodgeLaplacian_domain {u : F} :
    u ∈ (hodgeLaplacian d₀ d₁).domain ↔
      (∃ h₀ : u ∈ d₀†.domain, d₀† ⟨u, h₀⟩ ∈ d₀††.domain) ∧
        ∃ h₁ : u ∈ d₁.domain, d₁ ⟨u, h₁⟩ ∈ d₁†.domain := by
  rw [hodgeLaplacian_def, add_domain, Submodule.mem_inf, mem_adjointComp_domain,
    mem_adjointComp_domain]

/-- Every vector in the domain of the Laplacian lies in the domain of `d₀†† d₀†`. -/
theorem hodgeLaplacian_domain_le_adjointComp_adjoint :
    (hodgeLaplacian d₀ d₁).domain ≤ d₀†.adjointComp.domain :=
  inf_le_left

/-- Every vector in the domain of the Laplacian lies in the domain of `d₁† d₁`. -/
theorem hodgeLaplacian_domain_le_adjointComp :
    (hodgeLaplacian d₀ d₁).domain ≤ d₁.adjointComp.domain :=
  inf_le_right

/-- Every vector in the domain of the Laplacian lies in the domain of `d₀†`. -/
theorem hodgeLaplacian_domain_le_adjoint_domain : (hodgeLaplacian d₀ d₁).domain ≤ d₀†.domain :=
  hodgeLaplacian_domain_le_adjointComp_adjoint.trans (adjointComp_domain_le _)

/-- Every vector in the domain of the Laplacian lies in the domain of `d₁`. -/
theorem hodgeLaplacian_domain_le_domain : (hodgeLaplacian d₀ d₁).domain ≤ d₁.domain :=
  hodgeLaplacian_domain_le_adjointComp.trans (adjointComp_domain_le _)

/-- The Laplacian is the sum of `d₀†† d₀†` and `d₁† d₁`. -/
theorem hodgeLaplacian_apply (u : (hodgeLaplacian d₀ d₁).domain) :
    hodgeLaplacian d₀ d₁ u =
      d₀†.adjointComp ⟨u, hodgeLaplacian_domain_le_adjointComp_adjoint u.property⟩ +
        d₁.adjointComp ⟨u, hodgeLaplacian_domain_le_adjointComp u.property⟩ :=
  add_apply _ _ u

/-- **The quadratic form of the Laplacian.** For `u` in the domain of the Laplacian and
`v ∈ dom d₀† ∩ dom d₁`, `⟪Δ u, v⟫ = ⟪d₀† u, d₀† v⟫ + ⟪d₁ u, d₁ v⟫`. -/
theorem inner_hodgeLaplacian (hc₀ : d₀.IsClosable) (hd₁ : Dense (d₁.domain : Set F))
    (u : (hodgeLaplacian d₀ d₁).domain) {v : F} (h₀ : v ∈ d₀†.domain) (h₁ : v ∈ d₁.domain) :
    ⟪hodgeLaplacian d₀ d₁ u, v⟫ =
      ⟪d₀† ⟨u, hodgeLaplacian_domain_le_adjoint_domain u.property⟩, d₀† ⟨v, h₀⟩⟫ +
        ⟪d₁ ⟨u, hodgeLaplacian_domain_le_domain u.property⟩, d₁ ⟨v, h₁⟩⟫ := by
  rw [hodgeLaplacian_apply, inner_add_left, inner_adjointComp (dense_adjoint_domain hc₀) _ h₀,
    inner_adjointComp hd₁ _ h₁]

/-- The quadratic form of the Laplacian is `‖d₀† u‖² + ‖d₁ u‖²`; in particular the Laplacian is
nonnegative. -/
theorem re_inner_hodgeLaplacian_self (hc₀ : d₀.IsClosable) (hd₁ : Dense (d₁.domain : Set F))
    (u : (hodgeLaplacian d₀ d₁).domain) :
    RCLike.re ⟪hodgeLaplacian d₀ d₁ u, (u : F)⟫ =
      ‖d₀† ⟨u, hodgeLaplacian_domain_le_adjoint_domain u.property⟩‖ ^ 2 +
        ‖d₁ ⟨u, hodgeLaplacian_domain_le_domain u.property⟩‖ ^ 2 := by
  rw [inner_hodgeLaplacian hc₀ hd₁ u (hodgeLaplacian_domain_le_adjoint_domain u.property)
    (hodgeLaplacian_domain_le_domain u.property), _root_.map_add, inner_self_eq_norm_sq,
    inner_self_eq_norm_sq]

/-- **The kernel of the Laplacian is the harmonic space** `ker d₁ ⊓ ker d₀†`. -/
theorem ker_hodgeLaplacian (hc₀ : d₀.IsClosable) (hd₁ : Dense (d₁.domain : Set F)) :
    (hodgeLaplacian d₀ d₁).ker = harmonicSpace d₀ d₁ := by
  ext u
  rw [mem_harmonicSpace_iff]
  constructor
  · intro hu
    obtain ⟨y, rfl, hy⟩ := mem_ker_iff.mp hu
    have h := re_inner_hodgeLaplacian_self hc₀ hd₁ y
    rw [hy, inner_zero_left, _root_.map_zero] at h
    have h₀ := sq_nonneg ‖d₀† ⟨(y : F), hodgeLaplacian_domain_le_adjoint_domain y.property⟩‖
    have h₁ := sq_nonneg ‖d₁ ⟨(y : F), hodgeLaplacian_domain_le_domain y.property⟩‖
    refine ⟨(coe_mem_ker_iff (x := ⟨(y : F), hodgeLaplacian_domain_le_domain y.property⟩)).2 ?_,
      (coe_mem_ker_iff
        (x := ⟨(y : F), hodgeLaplacian_domain_le_adjoint_domain y.property⟩)).2 ?_⟩
    · exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))
    · exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))
  · rintro ⟨hu₁, hu₀⟩
    have h₁ := d₁.ker_le_domain hu₁
    have h₀ := d₀†.ker_le_domain hu₀
    have e₁ : d₁ ⟨u, h₁⟩ = 0 := (coe_mem_ker_iff (x := ⟨u, h₁⟩)).1 hu₁
    have e₀ : d₀† ⟨u, h₀⟩ = 0 := (coe_mem_ker_iff (x := ⟨u, h₀⟩)).1 hu₀
    have hu : u ∈ (hodgeLaplacian d₀ d₁).domain := mem_hodgeLaplacian_domain.2
      ⟨⟨h₀, e₀ ▸ zero_mem _⟩, ⟨h₁, e₁ ▸ zero_mem _⟩⟩
    have z₀ (p) : d₀†† ⟨d₀† ⟨u, h₀⟩, p⟩ = 0 := (congrArg _ (Subtype.ext e₀)).trans (map_zero _)
    have z₁ (p) : d₁† ⟨d₁ ⟨u, h₁⟩, p⟩ = 0 := (congrArg _ (Subtype.ext e₁)).trans (map_zero _)
    refine (coe_mem_ker_iff (x := ⟨u, hu⟩)).2 ?_
    rw [hodgeLaplacian_apply, adjointComp_apply, adjointComp_apply, z₀, z₁, add_zero]

end Laplacian

/-! ### Self-adjointness -/

section SelfAdjoint

variable {d₀ : E →ₗ.[𝕜] F} {d₁ : F →ₗ.[𝕜] G}

omit [CompleteSpace F] in
/-- Pairing with the operator `T u = (d₀† u, d₁ u)` into `E ⊕ G`, whose `T†T` is the Laplacian. -/
private theorem inner_toLp_withLpProd_apply (a : E) (b : G) (u : (d₀†.withLpProd 2 d₁).domain) :
    ⟪WithLp.toLp 2 (a, b), d₀†.withLpProd 2 d₁ u⟫ =
      ⟪a, d₀† ⟨u, withLpProd_domain_le_left u.property⟩⟫ +
        ⟪b, d₁ ⟨u, withLpProd_domain_le_right u.property⟩⟫ := by
  rw [WithLp.prod_inner_apply, withLpProd_apply, WithLp.ofLp_toLp, WithLp.ofLp_toLp]

omit [CompleteSpace F] in
/-- In a complex, `v - P v` lies in the kernel of `d₀†`, where `P` is the orthogonal projection
onto the closed subspace `ker d₁`: `(ker d₁)ᗮ ≤ (range d₀)ᗮ = ker d₀†`. -/
private theorem sub_starProjection_mem_ker_adjoint (hd₀ : Dense (d₀.domain : Set E))
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) [d₁.ker.HasOrthogonalProjection] (v : F) :
    v - d₁.ker.starProjection v ∈ d₀†.ker := by
  rw [← orthogonal_range_eq_ker_adjoint hd₀]
  exact Submodule.orthogonal_le hcomplex (d₁.ker.sub_starProjection_mem_orthogonal v)

omit [CompleteSpace F] in
/-- The orthogonal projection `P` onto `ker d₁` maps `dom d₀†` into `dom d₀† ∩ ker d₁`. -/
private theorem starProjection_mem_adjoint_domain (hd₀ : Dense (d₀.domain : Set E))
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) [d₁.ker.HasOrthogonalProjection] {v : F}
    (hv : v ∈ d₀†.domain) : d₁.ker.starProjection v ∈ d₀†.domain := by
  simpa using d₀†.domain.sub_mem hv
    (d₀†.ker_le_domain (sub_starProjection_mem_ker_adjoint hd₀ hcomplex v))

omit [CompleteSpace F] in
/-- The orthogonal projection `P` onto `ker d₁` does not change `d₀†`. -/
private theorem adjoint_apply_starProjection (hd₀ : Dense (d₀.domain : Set E))
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) [d₁.ker.HasOrthogonalProjection]
    (v : d₀†.domain) :
    d₀† ⟨d₁.ker.starProjection v, starProjection_mem_adjoint_domain hd₀ hcomplex v.property⟩ =
      d₀† v := by
  have hk := sub_starProjection_mem_ker_adjoint hd₀ hcomplex (v : F)
  have e : (⟨d₁.ker.starProjection v, starProjection_mem_adjoint_domain hd₀ hcomplex
      v.property⟩ : d₀†.domain) = v - ⟨v - d₁.ker.starProjection v, d₀†.ker_le_domain hk⟩ :=
    Subtype.ext (by simp)
  rw [e, map_sub, (coe_mem_ker_iff (x := ⟨_, d₀†.ker_le_domain hk⟩)).1 hk, sub_zero]

/-- The domain `dom d₀† ∩ dom d₁` of `T` is dense: with `P` the orthogonal projection onto
`ker d₁`, it contains `P a + (b - P b)` for `a ∈ dom d₀†` and `b ∈ dom d₁`. -/
private theorem dense_withLpProd_adjoint_domain (hd₀ : Dense (d₀.domain : Set E))
    (hc₀ : d₀.IsClosable) (hc₁ : d₁.IsClosed) (hd₁ : Dense (d₁.domain : Set F))
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    Dense ((d₀†.withLpProd 2 d₁).domain : Set F) := by
  have : d₁.ker.HasOrthogonalProjection :=
    have := hc₁.isClosed_ker.completeSpace_coe
    inferInstance
  let P := d₁.ker.starProjection
  let φ : F × F → F := fun p ↦ P p.1 + (p.2 - P p.2)
  have hφ : Continuous φ :=
    (P.continuous.comp continuous_fst).add
      (continuous_snd.sub (P.continuous.comp continuous_snd))
  have hsurj : Function.Surjective φ := fun z ↦ ⟨(z, z), add_sub_cancel _ _⟩
  refine (hsurj.denseRange.dense_image hφ ((dense_adjoint_domain hc₀).prod hd₁)).mono ?_
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  refine (d₀†.withLpProd 2 d₁).domain.add_mem (mem_withLpProd_domain.mpr ⟨?_, ?_⟩)
    (mem_withLpProd_domain.mpr ⟨?_, ?_⟩)
  · exact starProjection_mem_adjoint_domain hd₀ hcomplex ha
  · exact d₁.ker_le_domain (d₁.ker.starProjection_apply_mem a)
  · exact d₀†.ker_le_domain (sub_starProjection_mem_ker_adjoint hd₀ hcomplex b)
  · exact d₁.domain.sub_mem hb (d₁.ker_le_domain (d₁.ker.starProjection_apply_mem b))

/-- **The adjoint of `T`.** The domain of `T†` is `dom d₀†† × dom d₁†`. -/
private theorem toLp_mem_adjoint_withLpProd_domain_iff (hd₀ : Dense (d₀.domain : Set E))
    (hc₀ : d₀.IsClosable) (hc₁ : d₁.IsClosed) (hd₁ : Dense (d₁.domain : Set F))
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) {a : E} {b : G} :
    WithLp.toLp 2 (a, b) ∈ (d₀†.withLpProd 2 d₁)†.domain ↔ a ∈ d₀††.domain ∧ b ∈ d₁†.domain := by
  constructor
  · intro h
    have : d₁.ker.HasOrthogonalProjection :=
      have := hc₁.isClosed_ker.completeSpace_coe
      inferInstance
    let P := d₁.ker.starProjection
    have key (v : (d₀†.withLpProd 2 d₁).domain) :
        ⟪(d₀†.withLpProd 2 d₁)† ⟨_, h⟩, (v : F)⟫ =
          ⟪a, d₀† ⟨v, withLpProd_domain_le_left v.property⟩⟫ +
            ⟪b, d₁ ⟨v, withLpProd_domain_le_right v.property⟩⟫ :=
      (adjoint_isFormalAdjoint (T := d₀†.withLpProd 2 d₁)
        (dense_withLpProd_adjoint_domain hd₀ hc₀ hc₁ hd₁ hcomplex) ⟨_, h⟩ v).trans
        (inner_toLp_withLpProd_apply a b v)
    constructor
    · -- Test `T†` against `P v ∈ dom d₀† ∩ ker d₁`, on which `T` is `(d₀† v, 0)`.
      refine mem_adjoint_domain_of_exists _ ⟨P ((d₀†.withLpProd 2 d₁)† ⟨_, h⟩), fun v ↦ ?_⟩
      have hPv₀ := starProjection_mem_adjoint_domain hd₀ hcomplex v.property
      have hPv₁ : P v ∈ d₁.ker := d₁.ker.starProjection_apply_mem v
      have hk := key ⟨P v, mem_withLpProd_domain.mpr ⟨hPv₀, d₁.ker_le_domain hPv₁⟩⟩
      rw [(coe_mem_ker_iff (x := ⟨P v, d₁.ker_le_domain hPv₁⟩)).1 hPv₁, inner_zero_right,
        add_zero] at hk
      rw [Submodule.inner_starProjection_left_eq_right]
      refine hk.trans ?_
      congr 1
      exact adjoint_apply_starProjection hd₀ hcomplex v
    · -- Test `T†` against `v - P v ∈ ker d₀† ∩ dom d₁`, on which `T` is `(0, d₁ v)`.
      refine mem_adjoint_domain_of_exists _
        ⟨(d₀†.withLpProd 2 d₁)† ⟨_, h⟩ - P ((d₀†.withLpProd 2 d₁)† ⟨_, h⟩), fun v ↦ ?_⟩
      have hPv₁ : P v ∈ d₁.ker := d₁.ker.starProjection_apply_mem v
      have hk₀ := sub_starProjection_mem_ker_adjoint hd₀ hcomplex (v : F)
      have hk₁ : (v : F) - P v ∈ d₁.domain := d₁.domain.sub_mem v.property (d₁.ker_le_domain hPv₁)
      have hk := key ⟨v - P v, mem_withLpProd_domain.mpr ⟨d₀†.ker_le_domain hk₀, hk₁⟩⟩
      rw [(coe_mem_ker_iff (x := ⟨_, d₀†.ker_le_domain hk₀⟩)).1 hk₀, inner_zero_right,
        zero_add] at hk
      have e : (⟨v - P v, hk₁⟩ : d₁.domain) = v - ⟨P v, d₁.ker_le_domain hPv₁⟩ := rfl
      have hval : d₁ ⟨v - P v, hk₁⟩ = d₁ v := by
        rw [e, map_sub, (coe_mem_ker_iff (x := ⟨P v, d₁.ker_le_domain hPv₁⟩)).1 hPv₁, sub_zero]
      rw [inner_sub_left, Submodule.inner_starProjection_left_eq_right, ← inner_sub_right]
      exact hk.trans (congrArg _ hval)
  · rintro ⟨ha, hb⟩
    refine mem_adjoint_domain_of_exists _ ⟨d₀†† ⟨a, ha⟩ + d₁† ⟨b, hb⟩, fun v ↦ ?_⟩
    rw [inner_add_left, inner_toLp_withLpProd_apply]
    exact congrArg₂ (· + ·)
      (adjoint_isFormalAdjoint (dense_adjoint_domain hc₀) ⟨a, ha⟩
        ⟨v, withLpProd_domain_le_left v.property⟩)
      (adjoint_isFormalAdjoint hd₁ ⟨b, hb⟩ ⟨v, withLpProd_domain_le_right v.property⟩)

/-- The Laplacian is `T†T`. -/
private theorem hodgeLaplacian_eq_adjointComp_withLpProd (hd₀ : Dense (d₀.domain : Set E))
    (hc₀ : d₀.IsClosable) (hc₁ : d₁.IsClosed) (hd₁ : Dense (d₁.domain : Set F))
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    hodgeLaplacian d₀ d₁ = (d₀†.withLpProd 2 d₁).adjointComp := by
  refine LinearPMap.ext ?_ fun u hf hg ↦ ?_
  · ext u
    rw [mem_hodgeLaplacian_domain, mem_adjointComp_domain]
    constructor
    · rintro ⟨⟨h₀, h₀'⟩, ⟨h₁, h₁'⟩⟩
      refine ⟨mem_withLpProd_domain.mpr ⟨h₀, h₁⟩, ?_⟩
      rw [withLpProd_apply]
      exact (toLp_mem_adjoint_withLpProd_domain_iff hd₀ hc₀ hc₁ hd₁ hcomplex).2 ⟨h₀', h₁'⟩
    · rintro ⟨hu, hT⟩
      rw [withLpProd_apply] at hT
      obtain ⟨h₀', h₁'⟩ := (toLp_mem_adjoint_withLpProd_domain_iff hd₀ hc₀ hc₁ hd₁ hcomplex).1 hT
      exact ⟨⟨withLpProd_domain_le_left hu, h₀'⟩, ⟨withLpProd_domain_le_right hu, h₁'⟩⟩
  · rw [adjointComp_apply]
    symm
    refine adjoint_apply_eq (T := d₀†.withLpProd 2 d₁)
      (dense_withLpProd_adjoint_domain hd₀ hc₀ hc₁ hd₁ hcomplex) _ fun v ↦ ?_
    rw [inner_hodgeLaplacian hc₀ hd₁ ⟨u, hf⟩ (withLpProd_domain_le_left v.property)
      (withLpProd_domain_le_right v.property), ← inner_toLp_withLpProd_apply]
    simp only [withLpProd_apply]

/-- **The Laplacian of a Hilbert complex is self-adjoint.** For `d₀` densely defined and
closable, `d₁` closed and densely defined and `range d₀ ≤ ker d₁`, the Laplacian
`d₀ d₀† + d₁† d₁` on its maximal domain is self-adjoint. -/
theorem isSelfAdjoint_hodgeLaplacian [CompleteSpace G] (hd₀ : Dense (d₀.domain : Set E))
    (hc₀ : d₀.IsClosable) (hc₁ : d₁.IsClosed) (hd₁ : Dense (d₁.domain : Set F))
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    IsSelfAdjoint (hodgeLaplacian d₀ d₁) := by
  rw [hodgeLaplacian_eq_adjointComp_withLpProd hd₀ hc₀ hc₁ hd₁ hcomplex]
  exact isSelfAdjoint_adjointComp _ (IsClosed.withLpProd (adjoint_isClosed hd₀) hc₁)
    (dense_withLpProd_adjoint_domain hd₀ hc₀ hc₁ hd₁ hcomplex)

/-- **Compact resolvent from the compactness property.** If a Hilbert complex has the
compactness property at `ε = id`, so that `dom d₀† ∩ dom d₁` with its graph norm embeds compactly
into `F`, then its Laplacian has compact resolvent: `(1 + Δ)⁻¹` maps the unit ball into the unit
ball of the graph norm. -/
theorem CompactProperty.hasCompactResolvent_hodgeLaplacian [CompleteSpace G]
    (h : CompactProperty d₀ d₁ (ContinuousLinearMap.id 𝕜 F)) (hd₀ : Dense (d₀.domain : Set E))
    (hc₀ : d₀.IsClosable) (hc₁ : d₁.IsClosed) (hd₁ : Dense (d₁.domain : Set F))
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (hodgeLaplacian d₀ d₁).HasCompactResolvent := by
  have hA := isSelfAdjoint_hodgeLaplacian hd₀ hc₀ hc₁ hd₁ hcomplex
  have hmem : (-1 : 𝕜) ∈ (hodgeLaplacian d₀ d₁).resolventSet := by
    simpa using hA.ofReal_mem_resolventSet_of_lt (γ := 0) (t := -1)
      (fun x ↦ by rw [zero_mul, re_inner_hodgeLaplacian_self hc₀ hd₁]; positivity)
      (by norm_num)
  refine HasCompactResolvent.of_isCompactOperator_resolvent hmem ?_
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall
    ((hodgeLaplacian d₀ d₁).resolvent _).toLinearMap one_pos).2 ?_
  refine ((compactProperty_id_iff d₀ d₁).1 h).of_isClosed_subset isClosed_closure
    (closure_mono ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hy1 : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.1 hy
  let x : (hodgeLaplacian d₀ d₁).domain := ⟨_, resolvent_mem_domain hmem y⟩
  have hx : hodgeLaplacian d₀ d₁ x = -(x : F) - y := by
    have := smul_sub_apply_resolvent hmem y
    rw [neg_one_smul] at this
    rw [← this]
    abel
  have hre := re_inner_hodgeLaplacian_self hc₀ hd₁ x
  rw [hx, inner_sub_left, inner_neg_left, _root_.map_sub, _root_.map_neg,
    inner_self_eq_norm_sq] at hre
  have hyx := neg_le_of_abs_le
    ((RCLike.abs_re_le_norm ⟪y, (x : F)⟫).trans (norm_inner_le_norm _ _))
  have hn₀ := norm_nonneg (d₀† ⟨x, hodgeLaplacian_domain_le_adjoint_domain x.property⟩)
  have hn₁ := norm_nonneg (d₁ ⟨x, hodgeLaplacian_domain_le_domain x.property⟩)
  have hnx := norm_nonneg (x : F)
  -- `‖x‖² + ‖d₀† x‖² + ‖d₁ x‖² = -re ⟪y, x⟫ ≤ ‖y‖ ‖x‖ ≤ ‖x‖`.
  have hsum : ‖(x : F)‖ ^ 2 +
      ‖d₀† ⟨x, hodgeLaplacian_domain_le_adjoint_domain x.property⟩‖ ^ 2 +
        ‖d₁ ⟨x, hodgeLaplacian_domain_le_domain x.property⟩‖ ^ 2 ≤ ‖(x : F)‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hy1 hnx]
  have hxle : ‖(x : F)‖ ≤ 1 := by nlinarith
  have h₀le : ‖d₀† ⟨x, hodgeLaplacian_domain_le_adjoint_domain x.property⟩‖ ≤ 1 := by nlinarith
  have h₁le : ‖d₁ ⟨x, hodgeLaplacian_domain_le_domain x.property⟩‖ ≤ 1 := by nlinarith
  exact ⟨hodgeLaplacian_domain_le_domain x.property,
    hodgeLaplacian_domain_le_adjoint_domain x.property, hxle, h₁le, h₀le⟩

end SelfAdjoint

/-! ### The range over `ℂ` -/

section Complex

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  {d₀ : E →ₗ.[ℂ] F} {d₁ : F →ₗ.[ℂ] G}

/-- **Solvability of `Δ u = f`.** For a complex Hilbert complex with the compactness property at
`ε = id`, the range of the Laplacian is the orthogonal complement of the harmonic space: `Δ u = f`
has a solution exactly when `f` is orthogonal to every harmonic vector. -/
theorem CompactProperty.range_hodgeLaplacian
    (h : CompactProperty d₀ d₁ (ContinuousLinearMap.id ℂ F)) (hd₀ : Dense (d₀.domain : Set E))
    (hc₀ : d₀.IsClosable) (hc₁ : d₁.IsClosed) (hd₁ : Dense (d₁.domain : Set F))
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    LinearMap.range (hodgeLaplacian d₀ d₁).toFun = (harmonicSpace d₀ d₁)ᗮ := by
  rw [← ker_hodgeLaplacian hc₀ hd₁]
  exact (isSelfAdjoint_hodgeLaplacian hd₀ hc₀ hc₁ hd₁ hcomplex).range_eq_orthogonal_ker
    (h.hasCompactResolvent_hodgeLaplacian hd₀ hc₀ hc₁ hd₁ hcomplex)

end Complex

end LinearPMap
