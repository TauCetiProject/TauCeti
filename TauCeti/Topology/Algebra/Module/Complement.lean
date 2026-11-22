/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Topology.Algebra.OpenMapping.BanachSchauder
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel
import TauCeti.Topology.Algebra.Group.FirstCountable
import TauCeti.Topology.Algebra.IsUniformGroup.Submodule

/-!
# Complemented submodules and continuous linear sections

Topological complementedness is preserved by continuous semilinear equivalences, allowing
continuous projections to be transported between different presentations of a module. It is also
preserved by restriction of scalars.
A continuous linear map is unchanged by the projection along its kernel onto a topological
complement of that kernel.
A continuous linear quotient map admits a continuous linear section exactly when its kernel is
continuously complemented; the section is obtained by descending the complementary projection
through the quotient.
A continuous linear functional taking a nonzero value on a vector `u` splits the space as the
product of the scalars and the kernel (`TauCeti.exists_homeomorph_prod_ker`).

For `T₀` complete first-countable uniform modules over a topological ring with a zero sequence of
units (`TauCeti.HasZeroSequenceOfUnits`), the Banach–Schauder open mapping theorem yields:
* `ContinuousLinearMap.equivProdOfSurjectiveOfIsComplOfComplete`: two surjective continuous linear
  maps with complementary kernels give an isomorphism `E ≃L[R] F × G`.
* `Submodule.IsCompl.isTopCompl_of_isClosed_of_complete`,
  `Submodule.isTopCompl_iff_isCompl_isClosed_of_complete`,
  `Submodule.ClosedComplemented.of_isCompl_isClosed_of_complete`, and
  `Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl_of_complete`: two closed
  algebraic complements are topological complements.

The companion closed-range criteria for a range admitting a closed complement or finite-dimensional
cokernel live in `TauCeti.Topology.Algebra.OpenMapping.ClosedRange`. The product equivalence and
closed-complement criteria generalize the normed-space results in
`Mathlib/Analysis/Normed/Module/Complemented.lean`.
-/

public section

namespace Submodule

section Map

variable {R S M N : Type*} [Ring R] [Ring S]
  [AddCommGroup M] [AddCommGroup N] [TopologicalSpace M] [TopologicalSpace N]
  [Module R M] [Module S N] {σ : R →+* S} {τ : S →+* R}
  [RingHomInvPair σ τ] [RingHomInvPair τ σ]

/-- A continuous semilinear equivalence carries a complemented submodule to a complemented
submodule. -/
theorem ClosedComplemented.map {p : Submodule R M} (hp : p.ClosedComplemented)
    (e : M ≃SL[σ] N) : (p.map e.toLinearMap).ClosedComplemented := by
  obtain ⟨P, hP⟩ := hp
  let ep := e.submoduleMap p
  refine ⟨ep.toContinuousLinearMap.comp (P.comp e.symm.toContinuousLinearMap), fun y ↦ ?_⟩
  simpa [ep] using congrArg ep (hP (ep.symm y))

/-- Complementedness is invariant under a continuous semilinear equivalence. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.closedComplemented_map_iff (e : M ≃SL[σ] N)
    (p : Submodule R M) : (p.map e.toLinearMap).ClosedComplemented ↔ p.ClosedComplemented := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map e⟩
  have hmap : (p.map e.toLinearMap).map e.symm.toLinearMap = p := by
    ext x
    simp
  exact hmap ▸ h.map e.symm

end Map

section RestrictScalars

variable (R : Type*) {A M : Type*} [Ring R] [Ring A] [AddCommGroup M] [TopologicalSpace M]
  [Module R M] [Module A M] [SMul R A] [IsScalarTower R A M]

/-- A complemented submodule stays complemented after restricting scalars: a continuous
`A`-linear projection onto `p` is in particular a continuous `R`-linear one. -/
theorem ClosedComplemented.restrictScalars {p : Submodule A M} (hp : p.ClosedComplemented) :
    (p.restrictScalars R).ClosedComplemented := by
  obtain ⟨P, hP⟩ := hp
  exact ⟨ContinuousLinearMap.codRestrict
    (ContinuousLinearMap.restrictScalars R (p.subtypeL.comp P)) (p.restrictScalars R)
    fun x ↦ (P x).property, fun x ↦ Subtype.ext (congrArg Subtype.val (hP ⟨x, x.property⟩))⟩

end RestrictScalars

end Submodule

namespace ContinuousLinearMap

open Topology

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]

/-- A continuous linear map is unchanged by the projection along its kernel onto a topological
complement of that kernel. -/
theorem apply_projectionL_ker (f : E →L[R] F) {q : Submodule R E} (h : q.IsTopCompl f.ker)
    (x : E) : f (q.projectionL f.ker h x) = f x := by
  have hk : f (f.ker.projection q h.isCompl.symm x) = 0 :=
    LinearMap.mem_ker.mp (Submodule.projection_apply_mem _ x)
  simpa [hk] using congrArg f (Submodule.projection_add_projection_eq_self h.isCompl x)

variable [ContinuousSub E]

/-- A continuous linear quotient map admits a continuous linear right inverse if and only if its
kernel is continuously complemented. -/
theorem exists_rightInverse_iff_closedComplemented_ker (f : E →L[R] F) (hf : IsQuotientMap f) :
    (∃ s : F →L[R] E, Function.RightInverse s f) ↔ f.ker.ClosedComplemented := by
  refine ⟨fun ⟨s, hs⟩ ↦ f.closedComplemented_ker_of_rightInverse s hs, fun h ↦ ?_⟩
  obtain ⟨q, hq⟩ := h.exists_isTopCompl
  -- The projection onto `q` along `ker f` is constant on the fibres of `f`, so it descends
  -- through the quotient map `f` to the desired section.
  let g := q.projectionL f.ker hq.symm
  have hg : f.ker ≤ g.ker := (Submodule.ker_projectionL hq.symm).ge
  let s := f.toLinearMap.liftOfSurjective hf.surjective ⟨g.toLinearMap, hg⟩
  have hs (x : E) : s (f x) = g x := LinearMap.equivOfSurjective_apply hf.surjective hg
  refine ⟨⟨s, hf.continuous_iff.mpr (g.continuous.congr fun x ↦ (hs x).symm)⟩, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hf.surjective y
  exact (congrArg f (hs x)).trans (f.apply_projectionL_ker hq.symm x)

end ContinuousLinearMap

namespace TauCeti

section KerProd

variable {𝕜 E : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]

/-- **Coordinates along a vector** `u` on which a continuous linear functional `φ` takes the value
`L ≠ 0`, based at `p`: a homeomorphism `E ≃ₜ 𝕜 × ker φ` sending `x` to
`(φ (x - p), (x - p) - (φ (x - p) / L) • u)`, with inverse `y ↦ p + (y.1 / L) • u + y.2`. -/
theorem exists_homeomorph_prod_ker {φ : StrongDual 𝕜 E} {u : E} {L : 𝕜} (hu : φ u = L)
    (hL : L ≠ 0) (p : E) :
    ∃ e : E ≃ₜ 𝕜 × LinearMap.ker (φ : E →ₗ[𝕜] 𝕜), (∀ x, (e x).1 = φ (x - p)) ∧
      (∀ x, ((e x).2 : E) = (x - p) - (φ (x - p) / L) • u) ∧
      ∀ y, e.symm y = p + (y.1 / L) • u + y.2 := by
  let ψ : 𝕜 →L[𝕜] E := ContinuousLinearMap.toSpanSingleton 𝕜 (L⁻¹ • u)
  have hψ (r : 𝕜) : ψ r = (r / L) • u := by
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_smul, div_eq_mul_inv]
  have hψφ : Function.RightInverse ψ φ := fun r ↦ by
    rw [hψ, map_smul, hu, smul_eq_mul, div_mul_cancel₀ _ hL]
  refine ⟨(Homeomorph.subRight p).trans
    (ContinuousLinearEquiv.equivOfRightInverse φ ψ hψφ).toHomeomorph, fun x ↦ ?_, fun x ↦ ?_,
    fun y ↦ ?_⟩
  · simp only [Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph,
      ContinuousLinearEquiv.fst_equivOfRightInverse, Homeomorph.coe_subRight]
  · simp only [Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph,
      ContinuousLinearEquiv.snd_equivOfRightInverse, Homeomorph.coe_subRight, hψ]
  · simp only [Homeomorph.symm_trans_apply, ContinuousLinearEquiv.coe_symm_toHomeomorph,
      ContinuousLinearEquiv.equivOfRightInverse_symm_apply, hψ, Homeomorph.subRight_symm_apply]
    abel

end KerProd

end TauCeti

section BanachSchauderComplement

open Filter Function Topology
open scoped Uniformity

namespace ContinuousLinearMap

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E] [ContinuousSMul R E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [CompleteSpace F]
  [(𝓝 (0 : F)).IsCountablyGenerated] [T0Space F] [Module R F] [ContinuousConstSMul R F]

/-- If `f : E →L[R] F` and `g : E →L[R] G` are surjective continuous linear maps between complete
first-countable uniform modules (with `T₀` targets) over a topological ring with a zero sequence of
units whose kernels are algebraic complements, then `x ↦ (f x, g x)` defines a continuous linear
equivalence `E ≃L[R] F × G`. -/
noncomputable def equivProdOfSurjectiveOfIsComplOfComplete {G : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] [T0Space G] [Module R G] [ContinuousConstSMul R G]
    (f : E →L[R] F) (g : E →L[R] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
    (hfg : IsCompl f.ker g.ker) : E ≃L[R] F × G :=
  (f.toLinearMap.equivProdOfSurjectiveOfIsCompl g.toLinearMap hf hg
    hfg).toContinuousLinearEquivOfContinuousOfComplete (f.continuous.prodMk g.continuous)

@[simp]
theorem equivProdOfSurjectiveOfIsComplOfComplete_toLinearEquiv {G : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] [T0Space G] [Module R G] [ContinuousConstSMul R G]
    (f : E →L[R] F) (g : E →L[R] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
    (hfg : IsCompl f.ker g.ker) :
    (f.equivProdOfSurjectiveOfIsComplOfComplete g hf hg hfg).toLinearEquiv =
      f.toLinearMap.equivProdOfSurjectiveOfIsCompl g.toLinearMap hf hg hfg := by
  dsimp only [equivProdOfSurjectiveOfIsComplOfComplete]
  exact LinearEquiv.toLinearEquiv_toContinuousLinearEquivOfContinuousOfComplete _ _

@[simp]
theorem equivProdOfSurjectiveOfIsComplOfComplete_apply {G : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] [T0Space G] [Module R G] [ContinuousConstSMul R G]
    (f : E →L[R] F) (g : E →L[R] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
    (hfg : IsCompl f.ker g.ker) (x : E) :
    f.equivProdOfSurjectiveOfIsComplOfComplete g hf hg hfg x = (f x, g x) := by
  dsimp only [equivProdOfSurjectiveOfIsComplOfComplete]
  exact (LinearEquiv.toContinuousLinearEquivOfContinuousOfComplete_apply _ _ x).trans
    (LinearMap.equivProdOfSurjectiveOfIsCompl_apply hf hg hfg x)

@[simp]
theorem coe_equivProdOfSurjectiveOfIsComplOfComplete {G : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] [T0Space G] [Module R G] [ContinuousConstSMul R G]
    (f : E →L[R] F) (g : E →L[R] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
    (hfg : IsCompl f.ker g.ker) :
    (f.equivProdOfSurjectiveOfIsComplOfComplete g hf hg hfg : E →L[R] F × G) = f.prod g := by
  ext x <;>
    simp only [ContinuousLinearEquiv.coe_coe, equivProdOfSurjectiveOfIsComplOfComplete_apply,
      prod_apply]

end ContinuousLinearMap

namespace Submodule

variable {R E : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [T0Space E] [Module R E] [ContinuousSMul R E]
  {p q : Submodule R E}

/-- In a `T₀` complete first-countable uniform module over a topological ring with a zero sequence
of units, two closed algebraic complements are topological complements (`Submodule.IsTopCompl`). -/
theorem IsCompl.isTopCompl_of_isClosed_of_complete (h : IsCompl p q)
    (hp : IsClosed (p : Set E)) (hq : IsClosed (q : Set E)) : IsTopCompl p q := by
  have : CompleteSpace p := hp.completeSpace_coe
  have : CompleteSpace q := hq.completeSpace_coe
  have : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  rw [IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl h]
  exact (p.prodEquivOfIsCompl q h).continuous_symm_of_complete (continuous_prodEquivOfIsCompl h)

/-- In a `T₀` complete first-countable uniform module over a topological ring with a zero sequence
of units, two submodules are topological complements if and only if they are closed algebraic
complements. -/
theorem isTopCompl_iff_isCompl_isClosed_of_complete :
    IsTopCompl p q ↔ IsCompl p q ∧ IsClosed (p : Set E) ∧ IsClosed (q : Set E) :=
  ⟨fun h ↦ ⟨h.isCompl, h.isClosed, h.isClosed'⟩,
    fun h ↦ IsCompl.isTopCompl_of_isClosed_of_complete h.1 h.2.1 h.2.2⟩

/-- A closed submodule admitting a closed algebraic complement in a `T₀` complete first-countable
uniform module over a topological ring with a zero sequence of units is topologically complemented
(`Submodule.ClosedComplemented`). -/
theorem ClosedComplemented.of_isCompl_isClosed_of_complete (h : IsCompl p q)
    (hp : IsClosed (p : Set E)) (hq : IsClosed (q : Set E)) : p.ClosedComplemented :=
  (IsCompl.isTopCompl_of_isClosed_of_complete h hp hq).closedComplemented

/-- In a `T₀` complete first-countable uniform module over a topological ring with a zero sequence
of units, a submodule is topologically complemented if and only if it is closed and admits a closed
algebraic complement. -/
theorem closedComplemented_iff_isClosed_exists_isClosed_isCompl_of_complete :
    p.ClosedComplemented ↔
      IsClosed (p : Set E) ∧ ∃ q : Submodule R E, IsClosed (q : Set E) ∧ IsCompl p q :=
  ⟨fun h ↦ ⟨h.isClosed, h.exists_isClosed_isCompl⟩,
    fun ⟨hp, _, hq, h⟩ ↦ .of_isCompl_isClosed_of_complete h hp hq⟩

end Submodule

end BanachSchauderComplement

end
