/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Topology.Algebra.OpenMapping.BanachSchauder
import TauCeti.Topology.Algebra.Group.FirstCountable
import TauCeti.Topology.Algebra.IsUniformGroup.Submodule

/-!
# Complemented submodules from the Banach–Schauder open mapping theorem

For `T₀` complete first-countable uniform modules over a topological ring with a zero sequence of
units (`TauCeti.HasZeroSequenceOfUnits`), the Banach–Schauder open mapping theorem yields:

* `ContinuousLinearMap.equivProdOfSurjectiveOfIsComplOfComplete`: two surjective continuous linear
  maps with complementary kernels give an isomorphism `E ≃L[R] F × G`.
* `Submodule.IsCompl.isTopCompl_of_isClosed_of_complete`,
  `Submodule.isTopCompl_iff_isCompl_isClosed_of_complete`,
  `Submodule.ClosedComplemented.of_isCompl_isClosed_of_complete`, and
  `Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl_of_complete`: two closed
  algebraic complements are topological complements.

These results generalize the normed-space complement criteria in
`Mathlib/Analysis/Normed/Module/Complemented.lean`. Companion closed-range criteria live in
`TauCeti.Topology.Algebra.OpenMapping.ClosedRange`.
-/

public section

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

@[simp]
theorem equivProdOfSurjectiveOfIsComplOfComplete_symm_apply_pair {G : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] [T0Space G] [Module R G] [ContinuousConstSMul R G]
    (f : E →L[R] F) (g : E →L[R] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
    (hfg : IsCompl f.ker g.ker) (x : E) :
    (f.equivProdOfSurjectiveOfIsComplOfComplete g hf hg hfg).symm (f x, g x) = x := by
  rw [← equivProdOfSurjectiveOfIsComplOfComplete_apply f g hf hg hfg x,
    ContinuousLinearEquiv.symm_apply_apply]

@[simp]
theorem apply_equivProdOfSurjectiveOfIsComplOfComplete_symm_fst {G : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] [T0Space G] [Module R G] [ContinuousConstSMul R G]
    (f : E →L[R] F) (g : E →L[R] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
    (hfg : IsCompl f.ker g.ker) (y : F × G) :
    f ((f.equivProdOfSurjectiveOfIsComplOfComplete g hf hg hfg).symm y) = y.1 := by
  have h := (f.equivProdOfSurjectiveOfIsComplOfComplete g hf hg hfg).apply_symm_apply y
  rw [equivProdOfSurjectiveOfIsComplOfComplete_apply] at h
  exact congrArg Prod.fst h

@[simp]
theorem apply_equivProdOfSurjectiveOfIsComplOfComplete_symm_snd {G : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] [T0Space G] [Module R G] [ContinuousConstSMul R G]
    (f : E →L[R] F) (g : E →L[R] G) (hf : f.range = ⊤) (hg : g.range = ⊤)
    (hfg : IsCompl f.ker g.ker) (y : F × G) :
    g ((f.equivProdOfSurjectiveOfIsComplOfComplete g hf hg hfg).symm y) = y.2 := by
  have h := (f.equivProdOfSurjectiveOfIsComplOfComplete g hf hg hfg).apply_symm_apply y
  rw [equivProdOfSurjectiveOfIsComplOfComplete_apply] at h
  exact congrArg Prod.snd h

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

end
