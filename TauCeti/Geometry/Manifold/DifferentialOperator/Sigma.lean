/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Sigma
public import TauCeti.RingTheory.Derivation.DifferentialOperator.Basic

/-!
# Differential operators on disjoint unions of manifolds

The smooth functions on a disjoint union `Σ i, M i` of manifolds on a common model are the
families of smooth functions on the components, and restriction to a component
(`TauCeti.sigmaRestrict i`) is a surjective algebra homomorphism. A family of operators `P i` on
the smooth functions on the components assembles into the operator `TauCeti.sigmaOperator P`
acting by `P i` on `M i`. Its commutator with multiplication by `f` is assembled from the
commutators of the `P i` with the restrictions of `f`, so it is a differential operator of order at
most `m`, in Grothendieck's sense of iterated commutators (`TauCeti.differentialOperators`),
exactly when every `P i` is. It is local when every `P i` is, so on a disjoint union of infinitely
many components a local operator need not have finite order; see
`TauCeti.Geometry.Manifold.DifferentialOperator.Peetre.Sigma`.

## Main declarations

* `TauCeti.sigmaOperator`: the operator acting componentwise by a family of operators, an algebra
  homomorphism from families of operators.
* `TauCeti.smulCommutator_sigmaOperator`: commutators with multiplication are taken
  componentwise.
* `TauCeti.sigmaOperator_mem_differentialOperators_iff`: the componentwise operator has order at
  most `m` exactly when each of its components has.
* `TauCeti.sigmaOperator_apply_eq_zero_of_eventuallyEq`: the componentwise operator of local
  operators is local.
-/

public section

noncomputable section

open Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace H (M i)]

/-! ### Componentwise operators -/

/-- The operator acting by `P i` on the component `M i`, before bundling. -/
private def sigmaOperatorAux (P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯) :
    Module.End ℝ C^∞⟮I, Σ i, M i; ℝ⟯ where
  toFun f := ⟨fun x ↦ P x.1 (sigmaRestrict x.1 f) x.2,
    contMDiff_sigma_iff.2 fun i ↦ (P i (sigmaRestrict i f)).contMDiff⟩
  -- Sums and scalar multiples of smooth maps are pointwise by definition: `ContMDiffMap.coe_add`
  -- and `ContMDiffMap.coe_smul` hold by `rfl`. Neither `simp` nor `rw` can apply them here,
  -- because the operations on the right come from the module structure used by `Module.End`
  -- and match those lemmas only after unfolding instances, so each goal is closed by `rfl`.
  map_add' f g := by ext; simp only [map_add]; rfl
  map_smul' c f := by ext; simp only [map_smul]; rfl

private theorem sigmaOperatorAux_apply (P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯)
    (f : C^∞⟮I, Σ i, M i; ℝ⟯) (x : Σ i, M i) :
    sigmaOperatorAux P f x = P x.1 (sigmaRestrict x.1 f) x.2 :=
  (rfl)

private theorem sigmaRestrict_sigmaOperatorAux (P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯) (i : ι)
    (f : C^∞⟮I, Σ i, M i; ℝ⟯) :
    sigmaRestrict i (sigmaOperatorAux P f) = P i (sigmaRestrict i f) := by
  ext x
  rw [sigmaRestrict_apply]
  exact sigmaOperatorAux_apply P f ⟨i, x⟩

/-- The operator on the smooth functions on a disjoint union `Σ i, M i` acting by `P i` on the
component `M i`, as an algebra homomorphism from families of operators. -/
def sigmaOperator :
    (∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯) →ₐ[ℝ] Module.End ℝ C^∞⟮I, Σ i, M i; ℝ⟯ where
  toFun := sigmaOperatorAux
  map_one' := by ext f ⟨i, x⟩; simp [sigmaOperatorAux_apply]
  map_mul' P Q := by
    ext f ⟨i, x⟩
    simp [sigmaOperatorAux_apply, sigmaRestrict_sigmaOperatorAux]
  map_zero' := by ext f ⟨i, x⟩; simp [sigmaOperatorAux_apply]
  map_add' _ _ := by ext f ⟨i, x⟩; simp [sigmaOperatorAux_apply]
  commutes' r := by
    ext f ⟨i, x⟩
    simp [sigmaOperatorAux_apply, Module.algebraMap_end_apply]

@[simp]
theorem sigmaOperator_apply_mk (P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯)
    (f : C^∞⟮I, Σ i, M i; ℝ⟯) (i : ι) (x : M i) :
    sigmaOperator P f ⟨i, x⟩ = P i (sigmaRestrict i f) x :=
  (rfl)

/-- Restricting the componentwise operator to `M i` gives its component `P i`. -/
@[simp]
theorem sigmaRestrict_sigmaOperator (P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯) (i : ι)
    (f : C^∞⟮I, Σ i, M i; ℝ⟯) :
    sigmaRestrict i (sigmaOperator P f) = P i (sigmaRestrict i f) :=
  sigmaRestrict_sigmaOperatorAux P i f

/-- The commutator of the componentwise operator with multiplication by `f` is the componentwise
operator of the commutators with the restrictions of `f`. -/
theorem smulCommutator_sigmaOperator (f : C^∞⟮I, Σ i, M i; ℝ⟯)
    (P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯) :
    smulCommutator ℝ f (sigmaOperator P) =
      sigmaOperator fun i ↦ smulCommutator ℝ (sigmaRestrict i f) (P i) := by
  ext g : 1
  exact sigmaRestrict_ext fun i ↦ by simp

/-- The componentwise operator has order at most `m` exactly when each of its components has. -/
theorem sigmaOperator_mem_differentialOperators_iff {P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯}
    {m : ℕ} :
    sigmaOperator P ∈
        differentialOperators ℝ C^∞⟮I, Σ i, M i; ℝ⟯ C^∞⟮I, Σ i, M i; ℝ⟯ C^∞⟮I, Σ i, M i; ℝ⟯ m ↔
      ∀ i, P i ∈ differentialOperators ℝ C^∞⟮I, M i; ℝ⟯ C^∞⟮I, M i; ℝ⟯ C^∞⟮I, M i; ℝ⟯ m := by
  refine ⟨fun h i ↦ mem_differentialOperators_of_comp_eq_comp (sigmaRestrict_surjective i)
    (LinearMap.ext fun f ↦ (sigmaRestrict_sigmaOperator P i f).symm) h, fun h ↦ ?_⟩
  induction m generalizing P with
  | zero =>
    refine mem_differentialOperators_zero_iff_smulCommutator.2 fun f ↦ ?_
    simp_rw [smulCommutator_sigmaOperator,
      smulCommutator_eq_zero_of_mem_differentialOperators_zero (h _)]
    exact map_zero sigmaOperator
  | succ m ih =>
    refine mem_differentialOperators_succ_iff.2 fun f ↦ ?_
    rw [smulCommutator_sigmaOperator]
    exact ih fun i ↦ smulCommutator_mem_differentialOperators (h i) _

/-- The componentwise operator of local operators is local: its value at `x` vanishes on every
function vanishing near `x`. -/
theorem sigmaOperator_apply_eq_zero_of_eventuallyEq {P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯}
    (hP : ∀ i (f : C^∞⟮I, M i; ℝ⟯) (x : M i), (f : M i → ℝ) =ᶠ[𝓝 x] 0 → P i f x = 0)
    {f : C^∞⟮I, Σ i, M i; ℝ⟯} {x : Σ i, M i} (hf : (f : (Σ i, M i) → ℝ) =ᶠ[𝓝 x] 0) :
    sigmaOperator P f x = 0 := by
  obtain ⟨i, y⟩ := x
  refine hP i _ y ?_
  filter_upwards [(continuous_sigmaMk.tendsto y).eventually hf] with z hz
  simpa using hz

end TauCeti
