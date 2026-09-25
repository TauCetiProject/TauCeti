/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Graph
public import TauCeti.Analysis.Calculus.Morse.Basic

/-!
# Intersections of the zero section with differential graphs

In a linear cotangent space, for differentiable `f`, the zero section meets the graph of `df`
precisely at the critical points of `f`. At a point where `f` and `df` are differentiable, the two
tangent spaces are complementary exactly when the Hessian is invertible. These identifications
are used when comparing Morse theory with the exact Floer theory of a zero section and
differential graph.

The statements use the continuous dual, as does the Liouville form on the normed cotangent model.
Transversality is the complementarity of the tangent subspaces in the product vector space. In
finite dimensions, injectivity of the Hessian suffices for this complementarity.

This is the linear cotangent-space model of the Morse--Floer comparison. See M. Audin and
M. Damian, *Morse Theory and Floer Homology*, Chapter 6.
-/

public section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The zero section in the normed linear cotangent space `V × StrongDual ℝ V`. -/
def strongDualCotangentZeroSection : Submodule ℝ (V × StrongDual ℝ V) :=
  LinearMap.range (LinearMap.inl ℝ V (StrongDual ℝ V))

/-- A point of the normed cotangent space lies in the zero section exactly when its covector
coordinate vanishes. -/
@[simp] theorem mem_strongDualCotangentZeroSection_iff (z : V × StrongDual ℝ V) :
    z ∈ strongDualCotangentZeroSection ↔ z.2 = 0 := by
  simp [strongDualCotangentZeroSection, LinearMap.range_inl]

/-- For differentiable `f`, intersection points of the zero section and differential graph,
expressed as a set of pairs, are precisely the critical points with zero cotangent covectors. -/
theorem strongDualCotangentZeroSection_inter_differential_graph (f : V → ℝ)
    (_hf : Differentiable ℝ f) :
    strongDualCotangentZeroSection.carrier ∩
      Set.range (fun x : V ↦ (x, fderiv ℝ f x)) =
        (fun x : V ↦ (x, (0 : StrongDual ℝ V))) '' {x | fderiv ℝ f x = 0} := by
  ext z
  constructor
  · rintro ⟨hz, x, rfl⟩
    have hx : fderiv ℝ f x = 0 := (mem_strongDualCotangentZeroSection_iff _).mp hz
    exact ⟨x, hx, by simp [hx]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(mem_strongDualCotangentZeroSection_iff _).mpr rfl,
      ⟨x, by exact Prod.ext rfl hx⟩⟩

/-- The zero section and the graph of a linear map meet only at the origin exactly when the map
is injective. This is the tangent-space part of transverse intersection. -/
theorem disjoint_strongDualCotangentZeroSection_graph_iff
    (A : V →ₗ[ℝ] StrongDual ℝ V) :
    Disjoint strongDualCotangentZeroSection A.graph ↔ Function.Injective A := by
  rw [disjoint_iff_inf_le]
  constructor
  · intro h u v huv
    have hker : A (u - v) = 0 := by simpa using sub_eq_zero.mpr huv
    have hp : (u - v, (0 : StrongDual ℝ V)) ∈
        strongDualCotangentZeroSection ⊓ A.graph := by
      simp [hker]
    have hz := h hp
    have : u - v = 0 := congrArg Prod.fst ((Submodule.mem_bot ℝ).mp hz)
    exact sub_eq_zero.mp this
  · intro h z hz
    have hA : A z.1 = 0 := by
      have hz0 := (mem_strongDualCotangentZeroSection_iff z).mp hz.1
      exact hz.2.symm.trans hz0
    have hz1 : z.1 = 0 := h (by simpa using hA)
    exact (Submodule.mem_bot ℝ).mpr (Prod.ext hz1
      ((mem_strongDualCotangentZeroSection_iff z).mp hz.1))

/-- The zero section and the graph of a linear map span the cotangent space exactly when the map
is surjective. -/
theorem codisjoint_strongDualCotangentZeroSection_graph_iff
    (A : V →ₗ[ℝ] StrongDual ℝ V) :
    Codisjoint strongDualCotangentZeroSection A.graph ↔ Function.Surjective A := by
  rw [Submodule.codisjoint_iff_exists_add_eq]
  constructor
  · intro h φ
    obtain ⟨u, v, hu, hv, heq⟩ := h (0, φ)
    refine ⟨v.1, ?_⟩
    have hu0 : u.2 = 0 := (mem_strongDualCotangentZeroSection_iff u).mp hu
    have hvA : v.2 = A v.1 := (LinearMap.mem_graph_iff A v).mp hv
    have hφ : u.2 + v.2 = φ := congrArg Prod.snd heq
    simpa [hu0, hvA] using hφ
  · intro h z
    obtain ⟨v, hv⟩ := h z.2
    refine ⟨(z.1 - v, 0), (v, A v), by simp, by simp, ?_⟩
    ext <;> simp [hv]

/-- The zero section and the graph of a linear map are complementary exactly when that map is
bijective. This statement also applies to infinite-dimensional normed spaces. -/
theorem isCompl_strongDualCotangentZeroSection_graph_iff
    (A : V →ₗ[ℝ] StrongDual ℝ V) :
    IsCompl strongDualCotangentZeroSection A.graph ↔ Function.Bijective A := by
  rw [isCompl_iff, disjoint_strongDualCotangentZeroSection_graph_iff,
    codisjoint_strongDualCotangentZeroSection_graph_iff]
  rfl

/-- When `f` and `df` are differentiable at `x`, the zero section is transverse to the tangent of
the graph of `df` exactly when the Hessian is invertible. The second derivative is viewed as a map
into the continuous dual. -/
theorem isCompl_strongDualCotangentZeroSection_range_fderiv_differential_graph_iff
    [FiniteDimensional ℝ V] {f : V → ℝ} {x : V}
    (_hf : DifferentiableAt ℝ f x) (hdf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    IsCompl strongDualCotangentZeroSection
      (LinearMap.range (fderiv ℝ (fun y : V ↦ (y, fderiv ℝ f y)) x).toLinearMap) ↔
        (fderiv ℝ (fderiv ℝ f) x).IsInvertible := by
  rw [fderiv_cotangent_differential_graph hdf]
  have hgraph : LinearMap.range
      ((ContinuousLinearMap.id ℝ V).prod (fderiv ℝ (fderiv ℝ f) x)).toLinearMap =
        (fderiv ℝ (fderiv ℝ f) x).toLinearMap.graph := by
    simpa only [ContinuousLinearMap.coe_prod, ContinuousLinearMap.coe_id] using
      (LinearMap.graph_eq_range_prod (fderiv ℝ (fderiv ℝ f) x).toLinearMap).symm
  rw [hgraph, isCompl_strongDualCotangentZeroSection_graph_iff]
  exact ⟨fun h ↦ ContinuousLinearMap.isInvertible_of_injective h.1,
    fun h ↦ ⟨h.injective, h.surjective⟩⟩

/-- At a `C²` critical point, the zero section and differential graph are transverse precisely
when the point is nondegenerate in the Morse sense. -/
theorem isNondegenerateCriticalPoint_iff_transverse_differential_graph
    [FiniteDimensional ℝ V] {f : V → ℝ} {x : V}
    (hf : ContDiffAt ℝ 2 f x) (hcrit : fderiv ℝ f x = 0) :
    IsNondegenerateCriticalPoint f x ↔
      IsCompl strongDualCotangentZeroSection
        (LinearMap.range (fderiv ℝ (fun y : V ↦ (y, fderiv ℝ f y)) x).toLinearMap) := by
  rw [isCompl_strongDualCotangentZeroSection_range_fderiv_differential_graph_iff
    (hf.differentiableAt (by norm_num))
    (ContDiffAt.hasFDerivAt_fderiv hf le_rfl).differentiableAt]
  exact ⟨fun h ↦ h.isInvertible, fun h ↦ ⟨hf, hcrit, h⟩⟩

end TauCeti

end
