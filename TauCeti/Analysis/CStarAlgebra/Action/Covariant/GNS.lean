/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.Generator.Basic
public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.OneParameter
import Mathlib.Topology.UniformSpace.UniformApproximation
import TauCeti.Analysis.CStarAlgebra.Action.Generator.Resolvent
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# The GNS covariant representation of an invariant positive functional

Let `α` be a point-norm continuous action of a topological group `G` on a possibly nonunital
C⋆-algebra `A`, and let `f` be a positive linear functional with `f (α g a) = f a`. On Mathlib's
GNS Hilbert space `f.GNS`, the completion of `A` for the semi-inner product `⟪a, b⟫ = f (a⋆ b)`,
the assignment `[b] ↦ [α_g b]` preserves inner products by invariance. Its extension to the
completion is a unitary representation of `G`, `CStarAction.gnsImplementingGroup`, the GNS
implementing group of `f`; its matrix coefficients between classes are
`⟪[a], U_g [b]⟫ = f (a⋆ α_g(b))`, `CStarAction.inner_gnsImplementingGroup_apply_coe`.

The representation is strongly continuous. Orbits of classes are continuous because positive
functionals on C⋆-algebras are bounded, so the class map `A → f.PreGNS` is continuous. Every
vector of the completion is a uniform limit of classes, and the operators are isometric, so
continuity passes to all orbits.

Together with Mathlib's GNS representation `f.gnsNonUnitalStarAlgHom`, the implementing group
satisfies `U_g π(a) = π(α_g(a)) U_g`. This is the covariant pair
`CStarAction.gnsCovariantRepresentation`. For `β ≠ 0` every β-KMS state is invariant,
`CStarAction.IsKMSState.apply_action`, so each such state has a GNS implementing group.

For a real action `α`, the implementing group `U_t` is a strongly continuous unitary group, so by
Stone's theorem it has a self-adjoint generator `H` with `U_t = exp (i t H)`, the *GNS
Hamiltonian* `CStarAction.gnsHamiltonian`. The class of every element `a` of the domain of the
generator `δ` of `α` lies in the domain of `H`, and `H [a] = -i [δ(a)]`,
`CStarAction.gnsHamiltonian_apply_toPreGNS`. Consequently `⟪[b], H [a]⟫ = -i f (b⋆ δ(a))`. These
classes form a core for `H`: the closure of the restriction of `H` to them is `H`,
`CStarAction.gnsHamiltonian_hasCore`. Indeed, `1` lies in the resolvent set of `δ`, so every
vector `-i ξ - H ξ` is approximated by vectors `-i [b - δ(b)]` with `b` in the domain of `δ`, and
the shift `-i - H` of the symmetric operator `H` controls both `‖ξ‖` and `‖H ξ‖`.

## References

Bratteli–Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, second edition,
Section 2.3.3, Corollary 2.3.17, for the unitary implementation of an automorphism leaving a
state invariant; Corollary 3.1.7, for invariant cores.
-/

public section

noncomputable section

open PositiveLinearMap UniformSpace
open scoped ComplexOrder InnerProductSpace

namespace TauCeti.CStarAction

section ImplementingGroup

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A] [PartialOrder A]
  [StarOrderedRing A] (α : CStarAction G A) {f : A →ₚ[ℂ] ℂ}

/-- An automorphism leaving a positive functional invariant induces an isometry of its GNS
pre-Hilbert space. -/
private def preGNSIsometry (hf : ∀ g a, f (α g a) = f a) (g : G) :
    f.PreGNS →ₗᵢ[ℂ] f.PreGNS where
  toLinearMap := f.toPreGNS.toLinearMap ∘ₗ (α.toContinuousLinearMap g).toLinearMap ∘ₗ
    f.ofPreGNS.toLinearMap
  norm_map' b := by simp [preGNS_norm_def, ← map_star, ← map_mul, hf]

private theorem preGNSIsometry_apply (hf : ∀ g a, f (α g a) = f a) (g : G) (b : f.PreGNS) :
    preGNSIsometry α hf g b = f.toPreGNS (α g (f.ofPreGNS b)) := by
  simp [preGNSIsometry]

/-- The **GNS implementing group** of a positive functional `f` invariant under `α`: the unitary
representation of `G` on the GNS Hilbert space extending `[b] ↦ [α_g b]`. -/
def gnsImplementingGroup (hf : ∀ g a, f (α g a) = f a) : ContRepresentation ℂ G f.GNS :=
  .ofMonoidHom
    { toFun g := (preGNSIsometry α hf g).toContinuousLinearMap.completion
      map_one' := by
        ext v
        induction v using Completion.induction_on with
        | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
        | ih b => simp [preGNSIsometry_apply]
      map_mul' g h := by
        ext v
        induction v using Completion.induction_on with
        | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
        | ih b => simp [preGNSIsometry_apply, α.mul_apply] }

variable (hf : ∀ g a, f (α g a) = f a)

/-- The implementing group sends the class of `b` to the class of `α_g b`. -/
@[simp]
theorem gnsImplementingGroup_apply_coe (g : G) (b : f.PreGNS) :
    α.gnsImplementingGroup hf g b = (f.toPreGNS (α g (f.ofPreGNS b)) : f.GNS) :=
  -- By definition `U_g` is the completion of `preGNSIsometry α hf g`.
  (ContinuousLinearMap.completion_apply_coe _ b).trans <|
    congrArg _ (preGNSIsometry_apply α hf g b)

/-- The GNS implementing group is unitary. -/
theorem isUnitary_gnsImplementingGroup : (α.gnsImplementingGroup hf).IsUnitary := by
  refine (ContRepresentation.isUnitary_iff_norm_map _).2 fun g v => ?_
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_norm
  | ih b => simpa [Completion.norm_coe, preGNSIsometry_apply] using
      (preGNSIsometry α hf g).norm_map b

/-- Matrix coefficients of the implementing group between classes:
`⟪[a], U_g [b]⟫ = f (a⋆ α_g(b))`. -/
theorem inner_gnsImplementingGroup_apply_coe (g : G) (a b : A) :
    ⟪(f.toPreGNS a : f.GNS), α.gnsImplementingGroup hf g (f.toPreGNS b)⟫_ℂ =
      f (star a * α g b) := by
  simp [preGNS_inner_def]

/-- The GNS implementing group is strongly continuous. -/
theorem continuous_gnsImplementingGroup_apply (v : f.GNS) :
    Continuous fun g => α.gnsImplementingGroup hf g v := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨b, hb⟩ := Completion.denseRange_coe.exists_dist_lt v hε
  refine ⟨fun g => α.gnsImplementingGroup hf g b, ?_, fun g => hεu ?_⟩
  · simp only [gnsImplementingGroup_apply_coe]
    exact Completion.continuous_coe _ |>.comp <|
      f.continuous_toPreGNS.comp (α.continuous_orbit _)
  · rwa [((α.isUnitary_gnsImplementingGroup hf).isometry g).dist_eq]

/-- The **GNS covariant representation** of a positive functional `f` invariant under `α`: Mathlib's
GNS representation of `A` on `f.GNS`, together with the GNS implementing group. -/
def gnsCovariantRepresentation : CovariantRepresentation α f.GNS where
  coefficient := f.gnsNonUnitalStarAlgHom
  group := α.gnsImplementingGroup hf
  isUnitary := α.isUnitary_gnsImplementingGroup hf
  continuous_orbit := α.continuous_gnsImplementingGroup_apply hf
  covariance g a v := by
    induction v using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih b => simp

@[simp]
theorem gnsCovariantRepresentation_coefficient :
    (α.gnsCovariantRepresentation hf).coefficient = f.gnsNonUnitalStarAlgHom :=
  (rfl)

@[simp]
theorem gnsCovariantRepresentation_group :
    (α.gnsCovariantRepresentation hf).group = α.gnsImplementingGroup hf :=
  (rfl)

end ImplementingGroup

section Hamiltonian

/-! ### The GNS Hamiltonian of a real action -/

open Complex Filter TauCeti.Semigroups
open scoped Topology

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
  -- Each point of the graph of `H` is a limit of points of the graph of the restriction.
  refine .of_graph_subset_closure (α.isSelfAdjoint_gnsHamiltonian hf).isClosed hS ?_
  intro p hp
  obtain ⟨ξ, rfl⟩ := H.mem_graph_iff'.mp hp
  obtain ⟨b, hb, hHb⟩ := α.exists_tendsto_gnsHamiltonian hf ξ
  refine mem_closure_of_tendsto (hb.prodMk_nhds hHb) (Eventually.of_forall fun n => ?_)
  have hmem : (f.toPreGNS (b n) : f.GNS) ∈ (H.domRestrict S).domain :=
    ⟨Submodule.mem_map.mpr ⟨b n, (b n).2, by simp⟩,
      α.toPreGNS_mem_gnsHamiltonian_domain hf (b n)⟩
  exact (H.domRestrict S).mem_graph_iff.mpr
    ⟨⟨_, hmem⟩, rfl, LinearPMap.domRestrict_apply rfl⟩

end Hamiltonian

end TauCeti.CStarAction
