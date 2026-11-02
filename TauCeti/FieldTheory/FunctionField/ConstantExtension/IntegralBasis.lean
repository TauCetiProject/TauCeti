/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic

/-!
# Constants form integral bases in a constant field extension

Let `F' = F · k'` be a finite separable constant field extension of a field `F` with exact
constant field `k`, and let `P` be a place of `F / k`.  A basis of constants — the `F`-basis of
`F'` given by a `k`-basis of `k'` — is an integral basis at `P`: its `𝒪_P`-span is the integral
closure of `𝒪_P` in `F'`.  Both the basis and its trace dual consist of constants, which are
integral over `𝒪_P`, and a basis whose trace dual is integral is an integral basis.

So the elements of `F'` integral over `𝒪_P` are exactly the `𝒪_P`-combinations of constants: the
local model of a constant field extension at `P` is `𝒪_P ⊗[k] k'`.  This is the local input to
the comparison of the Riemann–Roch spaces of `F / k` and `F' / k'`.

Without separability, the two sides of this equality are still defined and compared: the
`k'`-span `𝒪_P · k'` of `𝒪_P` in `F'` lies in the integral closure `𝒪'_P` of `𝒪_P` in `F'`, and
when `[F' : F] = [k' : k]` its elements are those whose coordinates in a basis of constants lie in
`𝒪_P`. Over an imperfect field the inclusion can be strict; its failure measures the genus drop
(`TauCeti.Place.singularityDegree`).

## Main definitions

* `TauCeti.Place.constantSpanIntegers`: the `k'`-span `𝒪_P · k'` of `𝒪_P` in `F'`.
* `TauCeti.Place.integralClosureSubmodule`: the integral closure `𝒪'_P` of `𝒪_P` in `F'`.

## Main results

* `TauCeti.Place.isIntegralBasis_constantBasis`: a basis of constants is an integral basis at
  every place of `F / k`.
* `TauCeti.Place.constantSpanIntegers_le_iff`: `𝒪_P · k'` is the smallest `k'`-subspace of `F'`
  containing the image of `𝒪_P`.
* `TauCeti.Place.mem_constantSpanIntegers_iff`: `𝒪_P · k'` in the coordinates of a basis of
  constants.
* `TauCeti.Place.constantSpanIntegers_le_integralClosureSubmodule`: `𝒪_P · k' ⊆ 𝒪'_P`.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6, the proof of
Theorem 3.6.3.
-/

public section

open Module

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- **A basis of constants is an integral basis at every place** (Stichtenoth, proof of
Theorem 3.6.3): for a finite separable extension of constants `k' / k` with `k` exact in `F` and
`F' = F · k'`, the `𝒪_P`-span of the image of a `k`-basis of `k'` is the integral closure of `𝒪_P`
in `F'`, for every place `P` of `F / k`. -/
theorem isIntegralBasis_constantBasis [Algebra.IsSeparable k k'] (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) {ι : Type*} [Finite ι] (b : Basis ι k k')
    (P : Place k F) : P.IsIntegralBasis F' (constantBasis hex h b) := by
  classical
  have := Module.Finite.of_basis b
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
  have := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') h
  refine IsIntegralBasis.of_isIntegral_of_isIntegral_traceDual F' P _ (fun i ↦ ?_) fun i ↦ ?_
  · rw [constantBasis_apply]
    exact isIntegral_integers_algebraMap P _
  · rw [traceDual_constantBasis, constantBasis_apply]
    exact isIntegral_integers_algebraMap P _

section ConstantSpan

variable (k' F') (P : Place k F)

/-- The `k'`-span `𝒪_P · k'` of the valuation ring of `P` inside `F'`. When `F` and `k'` are
linearly disjoint over `k`, so that `F' = F ⊗_k k'`, this is `𝒪_P ⊗_k k'`: the semilocal ring along
the fiber over `P` of the curve of `F / k` after extending the constants to `k'`. -/
noncomputable def constantSpanIntegers : Submodule k' F' :=
  Submodule.span k' (algebraMap F F' '' P.integers)

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
theorem constantSpanIntegers_def :
    constantSpanIntegers k' F' P = Submodule.span k' (algebraMap F F' '' P.integers) :=
  (rfl)

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
variable {P} in
theorem algebraMap_mem_constantSpanIntegers {f : F} (hf : f ∈ P.integers) :
    algebraMap F F' f ∈ constantSpanIntegers k' F' P :=
  Submodule.subset_span ⟨f, hf, rfl⟩

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- `𝒪_P · k'` is the smallest `k'`-subspace of `F'` containing the image of `𝒪_P`. -/
theorem constantSpanIntegers_le_iff {N : Submodule k' F'} :
    constantSpanIntegers k' F' P ≤ N ↔ ∀ f ∈ P.integers, algebraMap F F' f ∈ N := by
  rw [constantSpanIntegers_def, Submodule.span_le, Set.image_subset_iff]
  rfl

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
@[simp]
theorem one_mem_constantSpanIntegers : (1 : F') ∈ constantSpanIntegers k' F' P := by
  simpa using algebraMap_mem_constantSpanIntegers k' F' (one_mem P.integers)

omit [Algebra k k'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
variable {P} in
/-- `𝒪_P · k'` is closed under multiplication. -/
theorem mul_mem_constantSpanIntegers {x y : F'} (hx : x ∈ constantSpanIntegers k' F' P)
    (hy : y ∈ constantSpanIntegers k' F' P) : x * y ∈ constantSpanIntegers k' F' P := by
  have hxy := Submodule.mul_mem_mul hx hy
  rw [constantSpanIntegers_def, Submodule.span_mul_span] at hxy
  refine Submodule.span_mono ?_ hxy
  rintro _ ⟨_, ⟨f, hf, rfl⟩, _, ⟨g, hg, rfl⟩, rfl⟩
  exact ⟨f * g, mul_mem hf hg, map_mul _ _ _⟩

end ConstantSpan

section FinrankEq

variable [FiniteDimensional k k'] (h : constantCompositum F k' F' = ⊤)
  (hn : finrank F F' = finrank k k')

/-- **`𝒪_P · k'` in coordinates**: an element of `F'` lies in `𝒪_P · k'` exactly when its
coordinates in a basis of constants lie in `𝒪_P`. -/
theorem mem_constantSpanIntegers_iff {ι : Type*} [Fintype ι] (b : Basis ι k k') (P : Place k F)
    {z : F'} :
    z ∈ P.constantSpanIntegers k' F' ↔
      ∀ j, (constantBasisOfFinrankEq h hn b).repr z j ∈ P.integers := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      intro j
      rw [Algebra.algebraMap_eq_smul_one, ← map_one (algebraMap k' F'), map_smul,
        Finsupp.smul_apply, smul_eq_mul, constantBasisOfFinrankEq_repr_algebraMap]
      exact mul_mem hf (P.algebraMap_mem_integers _)
    | zero => simp
    | add x y _ _ hx hy => intro j; simpa using add_mem (hx j) (hy j)
    | smul c x _ hx =>
      intro j
      have hcx : c • x = ∑ i, (constantBasisOfFinrankEq h hn b).repr x i •
          algebraMap k' F' (c * b i) := by
        conv_lhs => rw [← (constantBasisOfFinrankEq h hn b).sum_repr x]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [constantBasisOfFinrankEq_apply, map_mul, Algebra.smul_def, Algebra.smul_def,
          Algebra.smul_def]
        ring
      rw [hcx, map_sum, Finsupp.finsetSum_apply]
      refine sum_mem fun i _ ↦ ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, constantBasisOfFinrankEq_repr_algebraMap]
      exact mul_mem (hx i) (P.algebraMap_mem_integers _)
  · intro hz
    rw [← (constantBasisOfFinrankEq h hn b).sum_repr z]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [constantBasisOfFinrankEq_apply, Algebra.smul_def, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hz j, rfl⟩)

end FinrankEq

section IntegralClosure

variable (k' F') (P : Place k F) [Algebra.IsIntegral k k']

/-- The integral closure `𝒪'_P` of the valuation ring of `P` in `F'`, as a `k'`-subspace of `F'`.
Its elements are the functions regular at every place of `F' / k'` over `P`
(`TauCeti.Place.mem_integralClosureSubmodule_iff_forall_restrict_eq`). -/
noncomputable def integralClosureSubmodule : Submodule k' F' where
  carrier := {z | IsIntegral P.integers z}
  add_mem' ha hb := ha.add hb
  zero_mem' := isIntegral_zero
  smul_mem' c _ hz := by
    rw [Set.mem_ofPred_eq, Algebra.smul_def]
    exact (isIntegral_integers_algebraMap P c).mul hz

@[simp]
theorem mem_integralClosureSubmodule_iff {z : F'} :
    z ∈ integralClosureSubmodule k' F' P ↔ IsIntegral P.integers z :=
  (Iff.rfl)

theorem one_mem_integralClosureSubmodule : (1 : F') ∈ integralClosureSubmodule k' F' P :=
  isIntegral_one

variable {P} in
/-- `𝒪'_P` is closed under multiplication. -/
theorem mul_mem_integralClosureSubmodule {x y : F'} (hx : x ∈ integralClosureSubmodule k' F' P)
    (hy : y ∈ integralClosureSubmodule k' F' P) : x * y ∈ integralClosureSubmodule k' F' P :=
  IsIntegral.mul hx hy

/-- `𝒪'_P` consists of the functions regular at every place of `F' / k'` over `P`. -/
theorem mem_integralClosureSubmodule_iff_forall_restrict_eq [Algebra.IsIntegral F F']
    (hF' : IsFunctionField k' F') {z : F'} :
    z ∈ integralClosureSubmodule k' F' P ↔
      ∀ P' : Place k' F', P'.restrict k F = P → z ∈ P'.integers :=
  isIntegral_iff_forall_restrict_eq_mem_integers hF' P

/-- `𝒪_P · k'` lies in the integral closure of `𝒪_P`: functions of `𝒪_P` and constants of `k'`
are integral over `𝒪_P`. -/
theorem constantSpanIntegers_le_integralClosureSubmodule :
    constantSpanIntegers k' F' P ≤ integralClosureSubmodule k' F' P :=
  (constantSpanIntegers_le_iff k' F' P).2 fun f hf ↦
    isIntegral_algebraMap (x := (⟨f, hf⟩ : P.integers))

end IntegralClosure

end Place

end TauCeti
