/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.GNS
public import TauCeti.Analysis.CStarAlgebra.Action.GroundState.Basic
public import TauCeti.Analysis.CStarAlgebra.GNS
public import TauCeti.RepresentationTheory.Continuous.Unitary.OneParameter
import TauCeti.Analysis.CStarAlgebra.Action.Generator.Resolvent
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# The GNS Hamiltonian and ground states

Let `α` be a point-norm continuous real action on a possibly nonunital C⋆-algebra `A`, and let
`f` be an `α`-invariant positive functional. The GNS implementing group `U_t [b] = [α_t(b)]` is
a strongly continuous unitary group on the GNS Hilbert space, so by Stone's theorem it has a
self-adjoint generator `H` with `U_t = exp (i t H)`, the *GNS Hamiltonian*
`CStarAction.gnsHamiltonian`.

The class of every element `a` of the domain of the generator `δ` of `α` lies in the domain of
`H`, and `H [a] = -i [δ(a)]`, `CStarAction.gnsHamiltonian_apply_toPreGNS`. Consequently
`⟪[b], H [a]⟫ = -i f (b⋆ δ(a))`. These classes form a core for `H`: the closure of the
restriction of `H` to them is `H`, `CStarAction.gnsHamiltonian_hasCore`. Indeed, `1` lies in the
resolvent set of `δ`, so every vector `-i ξ - H ξ` is approximated by vectors `-i [b - δ(b)]`
with `b` in the domain of `δ`, and the shift `-i - H` of the symmetric operator `H` controls both
`‖ξ‖` and `‖H ξ‖`.

A ground state `ω` is invariant, and its GNS Hamiltonian is nonnegative,
`CStarAction.IsGroundState.inner_gnsHamiltonian_nonneg`: by the generator inequality
`-i ω (a⋆ δ(a)) ≥ 0` the quadratic form of `H` is nonnegative on the core. Conversely an invariant
state with nonnegative GNS Hamiltonian satisfies the generator inequality, and so is a ground
state. Thus the ground states are exactly the invariant states with nonnegative GNS Hamiltonian,
`CStarAction.isGroundState_iff_exists_inner_gnsHamiltonian_nonneg`.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Proposition 5.3.19, for the equivalence of the ground-state condition, the generator inequality,
and invariance with a positive GNS Hamiltonian; volume 1, Corollary 3.1.7, for invariant cores.
-/

public section

noncomputable section

open Complex Filter PositiveLinearMap TauCeti.Semigroups UniformSpace
open scoped ComplexOrder InnerProductSpace Topology

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (α : CStarAction (Multiplicative ℝ) A) {f : A →ₚ[ℂ] ℂ}

/-- The GNS implementing group of an invariant positive functional as a strongly continuous
one-parameter group. -/
private abbrev gnsGroup (hf : ∀ t a, f (α t a) = f a) : StronglyContinuousGroup f.GNS :=
  (α.gnsImplementingGroup hf).toStronglyContinuousGroup
    (α.continuous_gnsImplementingGroup_apply hf)

private theorem isUnitary_gnsGroup (hf : ∀ t a, f (α t a) = f a) : (α.gnsGroup hf).IsUnitary :=
  (α.isUnitary_gnsImplementingGroup hf).isUnitary_toStronglyContinuousGroup _

/-- The **GNS Hamiltonian** of a positive functional `f` invariant under a real action `α`: the
self-adjoint Stone generator `H` of the GNS implementing group, `U_t = exp (i t H)`. -/
def gnsHamiltonian (hf : ∀ t a, f (α t a) = f a) : f.GNS →ₗ.[ℂ] f.GNS :=
  (α.gnsGroup hf).stoneGenerator (α.isUnitary_gnsGroup hf)

variable (hf : ∀ t a, f (α t a) = f a)

theorem gnsHamiltonian_def :
    α.gnsHamiltonian hf = ((α.gnsImplementingGroup hf).toStronglyContinuousGroup
      (α.continuous_gnsImplementingGroup_apply hf)).stoneGenerator
      ((α.isUnitary_gnsImplementingGroup hf).isUnitary_toStronglyContinuousGroup _) :=
  (rfl)

/-- The GNS Hamiltonian is self-adjoint. -/
theorem isSelfAdjoint_gnsHamiltonian : IsSelfAdjoint (α.gnsHamiltonian hf) :=
  (α.gnsGroup hf).isSelfAdjoint_stoneGenerator _

/-- The orbit of the class of a domain element of `δ` has derivative `[δ(a)]` at `0`. -/
private theorem hasDerivAt_gnsGroup_toPreGNS (a : α.generator.domain) :
    HasDerivAt (fun t : ℝ => α.gnsGroup hf t (f.toPreGNS a))
      (f.toPreGNS (α.generator a) : f.GNS) 0 := by
  have h := (f.toGNS.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (α.hasDerivAt_zero a)
  simpa [Function.comp_def] using h

/-- The class of an element of the domain of the generator `δ` lies in the domain of the GNS
Hamiltonian. -/
theorem toPreGNS_mem_gnsHamiltonian_domain (a : α.generator.domain) :
    (f.toPreGNS a : f.GNS) ∈ (α.gnsHamiltonian hf).domain := by
  rw [gnsHamiltonian_def, StronglyContinuousGroup.stoneGenerator_domain,
    StronglyContinuousGroup.mem_complexDomain_iff]
  exact (α.gnsGroup hf).mem_domain_of_hasDerivAt_zero (α.hasDerivAt_gnsGroup_toPreGNS hf a)

/-- The GNS Hamiltonian acts on classes of domain elements of the generator `δ` by
`H [a] = -i [δ(a)]`. -/
@[simp]
theorem gnsHamiltonian_apply_toPreGNS (a : α.generator.domain) :
    α.gnsHamiltonian hf ⟨f.toPreGNS a, α.toPreGNS_mem_gnsHamiltonian_domain hf a⟩ =
      -I • (f.toPreGNS (α.generator a) : f.GNS) := by
  rw [LinearPMap.congr_fun (α.gnsHamiltonian_def hf) _
      (α.toPreGNS_mem_gnsHamiltonian_domain hf a), StronglyContinuousGroup.stoneGenerator_apply,
    StronglyContinuousGroup.complexGenerator_apply,
    (α.gnsGroup hf).generator_eq_of_hasDerivAt_zero (α.hasDerivAt_gnsGroup_toPreGNS hf a)]

/-- Matrix coefficients of the GNS Hamiltonian between classes:
`⟪[b], H [a]⟫ = -i f (b⋆ δ(a))`. -/
theorem inner_toPreGNS_gnsHamiltonian_apply_toPreGNS (b : A) (a : α.generator.domain) :
    ⟪(f.toPreGNS b : f.GNS),
        α.gnsHamiltonian hf ⟨f.toPreGNS a, α.toPreGNS_mem_gnsHamiltonian_domain hf a⟩⟫_ℂ =
      -I * f (star b * α.generator a) := by
  rw [gnsHamiltonian_apply_toPreGNS, inner_smul_right, Completion.inner_coe, preGNS_inner_def]
  simp

/-- Every vector `ξ` of the domain of the GNS Hamiltonian is the limit of classes `[b n]` of
domain elements of `δ` whose images `H [b n]` converge to `H ξ`. -/
private theorem exists_tendsto_gnsHamiltonian (ξ : (α.gnsHamiltonian hf).domain) :
    ∃ b : ℕ → α.generator.domain,
      Tendsto (fun n => (f.toPreGNS (b n) : f.GNS)) atTop (𝓝 ξ) ∧
      Tendsto (fun n => α.gnsHamiltonian hf
        ⟨f.toPreGNS (b n), α.toPreGNS_mem_gnsHamiltonian_domain hf (b n)⟩) atTop
        (𝓝 (α.gnsHamiltonian hf ξ)) := by
  have hH := IsSelfAdjoint.isFormalAdjoint (α.isSelfAdjoint_gnsHamiltonian hf)
  -- Approximate `i (-i ξ - H ξ)` by classes `[a n]`.
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp (f.denseRange_toGNS.closure_range ▸
    Set.mem_univ
    (I • (-I • (ξ : f.GNS) - α.gnsHamiltonian hf ξ)))
  choose a ha using hy
  replace ha : Tendsto (fun n => f.toGNS (a n)) atTop
      (𝓝 (I • (-I • (ξ : f.GNS) - α.gnsHamiltonian hf ξ))) := by
    simpa only [ha] using hlim
  -- Solve `b n - δ(b n) = a n` with the resolvent of `δ` at `1`.
  have hres := α.mem_resolventSet_generator (z := 1) (by simp)
  let b : ℕ → α.generator.domain := fun n =>
    ⟨LinearPMap.resolvent α.generator 1 (a n), LinearPMap.resolvent_mem_domain hres (a n)⟩
  have hb : ∀ n, ((b n : A) - α.generator (b n)) = a n := fun n => by
    simpa using LinearPMap.smul_sub_apply_resolvent hres (a n)
  -- The differences `x n = ξ - [b n]` satisfy `-i x n - H (x n) → 0`.
  let x : ℕ → (α.gnsHamiltonian hf).domain := fun n =>
    ξ - ⟨f.toPreGNS (b n), α.toPreGNS_mem_gnsHamiltonian_domain hf (b n)⟩
  have hshift :
      Tendsto (fun n => -I • (x n : f.GNS) - α.gnsHamiltonian hf (x n)) atTop (𝓝 0) := by
    have hx : ∀ n, -I • (x n : f.GNS) - α.gnsHamiltonian hf (x n) =
        (-I • (ξ : f.GNS) - α.gnsHamiltonian hf ξ) - -I • f.toGNS (a n) := fun n => by
      simp only [x, Submodule.coe_sub, LinearPMap.map_sub, gnsHamiltonian_apply_toPreGNS,
        ← hb, map_sub, toGNS_apply, smul_sub]
      abel
    have hlim := (tendsto_const_nhds (x := -I • (ξ : f.GNS) - α.gnsHamiltonian hf ξ)).sub
      (ha.const_smul (-I))
    rw [smul_smul, neg_mul, I_mul_I, neg_neg, one_smul, sub_self] at hlim
    simpa only [hx] using hlim
  have hxn : Tendsto (fun n => (x n : f.GNS)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_norm_zero.comp hshift)
    simpa using hH.norm_le_inv_abs_im_mul_norm_smul_sub (c := -I) (by simp) (x n)
  have hHxn : Tendsto (fun n => α.gnsHamiltonian hf (x n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_norm_zero.comp hshift)
    simpa using hH.norm_apply_le_mul_norm_smul_sub (c := -I) (by simp) (x n)
  refine ⟨b, ?_, ?_⟩
  · simpa [x] using (tendsto_const_nhds (x := (ξ : f.GNS))).sub hxn
  · simpa [x, LinearPMap.map_sub] using
      (tendsto_const_nhds (x := α.gnsHamiltonian hf ξ)).sub hHxn

/-- The classes of the domain elements of the generator `δ` form a core for the GNS Hamiltonian:
`H` is the closure of its restriction to them. -/
theorem gnsHamiltonian_hasCore :
    (α.gnsHamiltonian hf).HasCore (α.generator.domain.map f.toGNS.toLinearMap) := by
  set H := α.gnsHamiltonian hf
  set S := α.generator.domain.map f.toGNS.toLinearMap
  have hS : S ≤ H.domain := by
    rintro _ ⟨a, ha, rfl⟩
    simpa using α.toPreGNS_mem_gnsHamiltonian_domain hf ⟨a, ha⟩
  have hclosed : H.IsClosed := (α.isSelfAdjoint_gnsHamiltonian hf).isClosed
  have hT : (H.domRestrict S).IsClosable :=
    hclosed.isClosable.leIsClosable LinearPMap.domRestrict_le
  refine ⟨hS, le_antisymm (LinearPMap.le_of_le_graph ?_) (LinearPMap.le_of_le_graph ?_)⟩
  · -- The closure of the restriction lies in the closed graph of `H`.
    rw [← hT.graph_closure_eq_closure_graph]
    exact Submodule.topologicalClosure_minimal _
      (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le) hclosed
  · -- Each point of the graph of `H` is a limit of points of the graph of the restriction.
    intro p hp
    obtain ⟨ξ, h1, h2⟩ := H.mem_graph_iff.mp hp
    rw [← hT.graph_closure_eq_closure_graph, ← SetLike.mem_coe, Submodule.topologicalClosure_coe,
      ← Prod.mk.eta (p := p), ← h1, ← h2]
    obtain ⟨b, hb, hHb⟩ := α.exists_tendsto_gnsHamiltonian hf ξ
    refine mem_closure_of_tendsto (hb.prodMk_nhds hHb) (Eventually.of_forall fun n => ?_)
    have hmem : (f.toPreGNS (b n) : f.GNS) ∈ (H.domRestrict S).domain :=
      ⟨Submodule.mem_map.mpr ⟨b n, (b n).2, by simp⟩,
        α.toPreGNS_mem_gnsHamiltonian_domain hf (b n)⟩
    exact (H.domRestrict S).mem_graph_iff.mpr
      ⟨⟨_, hmem⟩, rfl, LinearPMap.domRestrict_apply rfl⟩

section GroundState

variable {ω : A →P[ℂ] ℂ}

/-- **The GNS Hamiltonian of a ground state is nonnegative**: `0 ≤ ⟪ξ, H ξ⟫` on its domain. -/
theorem IsGroundState.inner_gnsHamiltonian_nonneg (hω : α.IsGroundState ω)
    (hf : ∀ t a, (ω : A →ₚ[ℂ] ℂ) (α t a) = (ω : A →ₚ[ℂ] ℂ) a)
    (ξ : (α.gnsHamiltonian hf).domain) :
    0 ≤ ⟪(ξ : (ω : A →ₚ[ℂ] ℂ).GNS), α.gnsHamiltonian hf ξ⟫_ℂ := by
  obtain ⟨b, hb, hHb⟩ := α.exists_tendsto_gnsHamiltonian hf ξ
  refine isClosed_Ici.mem_of_tendsto (hb.inner (𝕜 := ℂ) hHb) (Eventually.of_forall fun n => ?_)
  rw [Set.mem_Ici, inner_toPreGNS_gnsHamiltonian_apply_toPreGNS]
  simpa using hω.neg_I_mul_apply_star_mul_generator_nonneg (b n)

/-- **Ground states are the invariant states with nonnegative GNS Hamiltonian.** A state `ω` is a
ground state of `α` exactly when it is `α`-invariant and its GNS Hamiltonian `H` satisfies
`0 ≤ ⟪ξ, H ξ⟫` on its domain. -/
theorem isGroundState_iff_exists_inner_gnsHamiltonian_nonneg :
    α.IsGroundState ω ↔ ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧
      ∃ hf : ∀ t a, (ω : A →ₚ[ℂ] ℂ) (α t a) = (ω : A →ₚ[ℂ] ℂ) a,
        ∀ ξ : (α.gnsHamiltonian hf).domain,
          0 ≤ ⟪(ξ : (ω : A →ₚ[ℂ] ℂ).GNS), α.gnsHamiltonian hf ξ⟫_ℂ := by
  refine ⟨fun hω => ⟨hω.norm_eq_one, fun t a => by simpa using hω.apply_action t a,
    hω.inner_gnsHamiltonian_nonneg α _⟩, fun ⟨hnorm, hf, h⟩ =>
    isGroundState_iff_neg_I_mul_apply_star_mul_generator_nonneg.mpr ⟨hnorm, fun a => ?_⟩⟩
  have ha := h ⟨_, α.toPreGNS_mem_gnsHamiltonian_domain hf a⟩
  rwa [inner_toPreGNS_gnsHamiltonian_apply_toPreGNS] at ha

end GroundState

end TauCeti.CStarAction
