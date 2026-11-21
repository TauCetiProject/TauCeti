/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Algebra.Lie.KacMoody.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.RootLattice
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

/-!
# Weight modules and category `O` for a presented Kac–Moody algebra

Let `R` be a realization of an integral square matrix `A` in a `K`-vector space `H`, and let
`Enveloping R` be the universal enveloping algebra of `TauCeti.KacMoody.PresentedLieAlgebra R`.
Working over `Enveloping R` puts submodules, quotients, products, direct sums, and simplicity on
Mathlib's ring-level `Module` infrastructure, while
`TauCeti.UniversalEnvelopingAlgebra` in `TauCeti.Algebra.Lie.UniversalEnveloping.Module` bridges
between `Enveloping R`-modules and Lie modules whenever Lie-module predicates are needed.

For any `Enveloping R`-module `M` whose `K`-action is compatible with the algebra structure of
`Enveloping R`, the Cartan and Chevalley generators act by `K`-linear endomorphisms
`cartanAction R M`, `positiveAction R M`, and `negativeAction R M`. For `μ ∈ Dual K H`, the weight
space `weightSpace R M μ` is the joint eigenspace `⨅ x : H, (cartanAction R M x).eigenspace (μ x)`.
The defining relations move weight vectors along simple roots: `positiveAction R M i` carries weight
`μ` into `μ + αᵢ` and `negativeAction R M i` carries `μ` into `μ - αᵢ`.

A module `M` is a *weight module* (`IsWeightModule R M`) when its weight spaces span `M`. Because
joint eigenspaces of any linear family are independent (`iSupIndep_weightSpace`) and non-linear
eigenvalue functions have trivial joint eigenspaces (`TauCeti.iSup_dual_eq_iSup`), every
`cartanAction`-invariant `K`-subspace — in particular every `Enveloping R`-submodule — decomposes as
the direct sum of its intersections with the weight spaces, over an arbitrary base field.

Category `O` (`IsCategoryO R M`) refines `IsWeightModule R M` by requiring finite-dimensional weight
spaces and a finite set `S` of weights whose downward cones `λ - Q₊` cover all weights of `M`. Both
`IsWeightModule` and `IsCategoryO` are closed under submodules, quotients, binary products, and
direct sums (finite direct sums for `IsCategoryO`). Over a field of characteristic zero, the height
homomorphism `CartanRealization.height` bounds upward chains in `⋃_{λ ∈ S} (λ - Q₊)`, so every
nonzero `Enveloping R`-submodule of a module in `IsCategoryO` has a `RootLE`-maximal weight and
therefore a nonzero primitive vector annihilated by every `positiveAction R M i` — with no
finiteness hypothesis on the index set `I`.

## Main definitions

* `TauCeti.KacMoody.Enveloping`: the universal enveloping algebra of `PresentedLieAlgebra R`.
* `TauCeti.KacMoody.lieAction`, `TauCeti.KacMoody.cartanAction`,
  `TauCeti.KacMoody.positiveAction`, `TauCeti.KacMoody.negativeAction`: the `K`-linear actions of
  the presented algebra and its Cartan, raising, and lowering generators on an
  `Enveloping R`-module.
* `TauCeti.KacMoody.weightSpace`: the joint eigenspace of `cartanAction R M` for a linear form `μ`,
  with `TauCeti.KacMoody.weightSpaceDirectSumEquiv` identifying weight spaces of a direct sum.
* `TauCeti.KacMoody.IsWeightModule`: predicate that the weight spaces span `M`.
* `TauCeti.KacMoody.IsCategoryO`: Kac's category `O` predicate (weight module with
  finite-dimensional weight spaces and weights bounded above by finitely many cones `λ - Q₊`).

## Main results

* `TauCeti.KacMoody.positiveAction_mem_weightSpace` and
  `TauCeti.KacMoody.negativeAction_mem_weightSpace`: ladder shifts by `±αᵢ`.
* `TauCeti.KacMoody.iSupIndep_weightSpace` and `TauCeti.KacMoody.IsWeightModule.isInternal`:
  weight spaces are independent, and internally decompose any weight module.
* `TauCeti.KacMoody.IsWeightModule.iSup_inf_weightSpace_eq`: every `Enveloping R`-submodule of a
  weight module is the supremum of its weight components.
* `TauCeti.KacMoody.IsWeightModule.submodule`, `TauCeti.KacMoody.IsWeightModule.quotient`,
  `TauCeti.KacMoody.IsWeightModule.prod`, `TauCeti.KacMoody.IsWeightModule.directSum`, and the
  corresponding closure theorems for `TauCeti.KacMoody.IsCategoryO`.
* `TauCeti.KacMoody.IsCategoryO.exists_maximal_weight_of_ne_bot` and
  `TauCeti.KacMoody.IsCategoryO.exists_primitive_vector_of_ne_bot`: existence of maximal weights and
  primitive vectors in nonzero submodules in characteristic zero.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §§3.6, 9.1, and 9.2.
-/

public section

open DirectSum Module

namespace TauCeti

namespace KacMoody

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}

/-- The universal enveloping algebra of `TauCeti.KacMoody.PresentedLieAlgebra R`. -/
abbrev Enveloping (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) : Type _ :=
  _root_.UniversalEnvelopingAlgebra K (PresentedLieAlgebra R)

/-! ### Actions of the generators -/

section GeneratorActions

variable (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
variable (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
  [IsScalarTower K (Enveloping R) M]

/-- The Lie algebra homomorphism from `PresentedLieAlgebra R` to `Module.End K M` induced by the
left `Enveloping R`-module action on `M`. -/
noncomputable def lieAction (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] : PresentedLieAlgebra R →ₗ⁅K⁆ Module.End K M :=
  (Algebra.lsmul K K M).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι K)

/-- The `K`-linear action of the realization `H` on an `Enveloping R`-module `M`. -/
noncomputable def cartanAction (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] : H →ₗ[K] Module.End K M :=
  (lieAction R M).toLinearMap ∘ₗ cartanElement R

/-- The `K`-linear endomorphism by which the raising generator `eᵢ` acts on `M`. -/
noncomputable def positiveAction (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] (i : I) : Module.End K M :=
  lieAction R M (positiveGenerator R i)

/-- The `K`-linear endomorphism by which the lowering generator `fᵢ` acts on `M`. -/
noncomputable def negativeAction (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] (i : I) : Module.End K M :=
  lieAction R M (negativeGenerator R i)

/-- `lieAction` on a Cartan element is `cartanAction`. -/
@[simp]
theorem lieAction_cartanElement (x : H) :
    lieAction R M (cartanElement R x) = cartanAction R M x := (rfl)

/-- `lieAction` on a raising generator is `positiveAction`. -/
@[simp]
theorem lieAction_positiveGenerator (i : I) :
    lieAction R M (positiveGenerator R i) = positiveAction R M i := (rfl)

/-- `lieAction` on a lowering generator is `negativeAction`. -/
@[simp]
theorem lieAction_negativeGenerator (i : I) :
    lieAction R M (negativeGenerator R i) = negativeAction R M i := (rfl)

theorem lieAction_apply (x : PresentedLieAlgebra R) (m : M) :
    lieAction R M x m = (_root_.UniversalEnvelopingAlgebra.ι K x : Enveloping R) • m := (rfl)

theorem cartanAction_apply (x : H) (m : M) :
    cartanAction R M x m =
      (_root_.UniversalEnvelopingAlgebra.ι K (cartanElement R x) : Enveloping R) • m := (rfl)

theorem positiveAction_apply (i : I) (m : M) :
    positiveAction R M i m =
      (_root_.UniversalEnvelopingAlgebra.ι K (positiveGenerator R i) : Enveloping R) • m := (rfl)

theorem negativeAction_apply (i : I) (m : M) :
    negativeAction R M i m =
      (_root_.UniversalEnvelopingAlgebra.ι K (negativeGenerator R i) : Enveloping R) • m := (rfl)

/-- The endomorphisms `cartanAction R M`, `positiveAction R M`, and `negativeAction R M` satisfy the
defining Chevalley and Serre relations of `R` in `Module.End K M`. -/
theorem satisfiesRelations_action :
    SatisfiesRelations R (cartanAction R M) (positiveAction R M) (negativeAction R M) :=
  (satisfiesRelations_generators R).map (lieAction R M)

@[simp]
theorem lie_cartanAction_cartanAction (x y : H) :
    ⁅cartanAction R M x, cartanAction R M y⁆ = 0 :=
  (satisfiesRelations_action R M).lie_cartan_cartan x y

theorem commute_cartanAction (x y : H) :
    Commute (cartanAction R M x) (cartanAction R M y) := by
  rw [commute_iff_eq, ← sub_eq_zero, ← Ring.lie_def]
  exact lie_cartanAction_cartanAction R M x y

@[simp]
theorem lie_cartanAction_positiveAction (x : H) (j : I) :
    ⁅cartanAction R M x, positiveAction R M j⁆ = R.root j x • positiveAction R M j :=
  (satisfiesRelations_action R M).lie_cartan_positive x j

theorem cartanAction_positiveAction_apply (x : H) (j : I) (m : M) :
    cartanAction R M x (positiveAction R M j m) =
      positiveAction R M j (cartanAction R M x m) + R.root j x • positiveAction R M j m := by
  have h := LinearMap.congr_fun (lie_cartanAction_positiveAction R M x j) m
  rw [Ring.lie_def, LinearMap.sub_apply, _root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp,
    LinearMap.smul_apply, sub_eq_iff_eq_add] at h
  rw [add_comm]
  exact h

@[simp]
theorem lie_cartanAction_negativeAction (x : H) (j : I) :
    ⁅cartanAction R M x, negativeAction R M j⁆ = -(R.root j x • negativeAction R M j) :=
  (satisfiesRelations_action R M).lie_cartan_negative x j

theorem cartanAction_negativeAction_apply (x : H) (j : I) (m : M) :
    cartanAction R M x (negativeAction R M j m) =
      negativeAction R M j (cartanAction R M x m) - R.root j x • negativeAction R M j m := by
  have h := LinearMap.congr_fun (lie_cartanAction_negativeAction R M x j) m
  rw [Ring.lie_def, LinearMap.sub_apply, _root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp,
    LinearMap.neg_apply, LinearMap.smul_apply, sub_eq_iff_eq_add] at h
  rw [h, sub_eq_add_neg, add_comm]

@[simp]
theorem lie_positiveAction_negativeAction_self (i : I) :
    ⁅positiveAction R M i, negativeAction R M i⁆ = cartanAction R M (R.coroot i) :=
  (satisfiesRelations_action R M).lie_positive_negative_self i

theorem positiveAction_negativeAction_self_apply (i : I) (m : M) :
    positiveAction R M i (negativeAction R M i m) =
      negativeAction R M i (positiveAction R M i m) + cartanAction R M (R.coroot i) m := by
  have h := LinearMap.congr_fun (lie_positiveAction_negativeAction_self R M i) m
  rw [Ring.lie_def, LinearMap.sub_apply, _root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp,
    sub_eq_iff_eq_add] at h
  rw [add_comm]
  exact h

@[simp]
theorem lie_positiveAction_negativeAction_of_ne {i j : I} (hij : i ≠ j) :
    ⁅positiveAction R M i, negativeAction R M j⁆ = 0 :=
  (satisfiesRelations_action R M).lie_positive_negative_of_ne i j hij

theorem commute_positiveAction_negativeAction_of_ne {i j : I} (hij : i ≠ j) :
    Commute (positiveAction R M i) (negativeAction R M j) := by
  rw [commute_iff_eq, ← sub_eq_zero, ← Ring.lie_def]
  exact lie_positiveAction_negativeAction_of_ne R M hij

@[simp]
theorem ad_pow_lie_positiveAction (i j : I) :
    (LieAlgebra.ad K (Module.End K M) (positiveAction R M i) ^ (-A i j).toNat)
      ⁅positiveAction R M i, positiveAction R M j⁆ = 0 :=
  (satisfiesRelations_action R M).serre_positive i j

@[simp]
theorem ad_pow_lie_negativeAction (i j : I) :
    (LieAlgebra.ad K (Module.End K M) (negativeAction R M i) ^ (-A i j).toNat)
      ⁅negativeAction R M i, negativeAction R M j⁆ = 0 :=
  (satisfiesRelations_action R M).serre_negative i j

variable {R M}
variable {N : Type*} [AddCommGroup N] [Module K N] [Module (Enveloping R) N]
  [IsScalarTower K (Enveloping R) N]

/-- Any `Enveloping R`-linear map intertwines `lieAction`. -/
@[simp]
theorem map_lieAction (f : M →ₗ[Enveloping R] N) (x : PresentedLieAlgebra R) (m : M) :
    f (lieAction R M x m) = lieAction R N x (f m) := by
  rw [lieAction_apply, lieAction_apply, map_smul]

/-- Any `Enveloping R`-linear map intertwines `cartanAction`. -/
@[simp]
theorem map_cartanAction (f : M →ₗ[Enveloping R] N) (x : H) (m : M) :
    f (cartanAction R M x m) = cartanAction R N x (f m) :=
  map_lieAction f (cartanElement R x) m

/-- Any `Enveloping R`-linear map intertwines `positiveAction`. -/
@[simp]
theorem map_positiveAction (f : M →ₗ[Enveloping R] N) (i : I) (m : M) :
    f (positiveAction R M i m) = positiveAction R N i (f m) :=
  map_lieAction f (positiveGenerator R i) m

/-- Any `Enveloping R`-linear map intertwines `negativeAction`. -/
@[simp]
theorem map_negativeAction (f : M →ₗ[Enveloping R] N) (i : I) (m : M) :
    f (negativeAction R M i m) = negativeAction R N i (f m) :=
  map_lieAction f (negativeGenerator R i) m

/-- Any `Enveloping R`-linear map intertwines powers of `lieAction`. -/
@[simp]
theorem map_lieAction_pow (f : M →ₗ[Enveloping R] N) (x : PresentedLieAlgebra R)
    (k : ℕ) (m : M) :
    f ((lieAction R M x ^ k) m) = (lieAction R N x ^ k) (f m) := by
  rw [_root_.pow_apply_eq_iterate, _root_.pow_apply_eq_iterate]
  exact Function.Semiconj.iterate_right (map_lieAction f x) k m

/-- Any `Enveloping R`-linear map intertwines powers of `cartanAction`. -/
@[simp]
theorem map_cartanAction_pow (f : M →ₗ[Enveloping R] N) (x : H) (k : ℕ) (m : M) :
    f ((cartanAction R M x ^ k) m) = (cartanAction R N x ^ k) (f m) :=
  map_lieAction_pow f (cartanElement R x) k m

/-- Any `Enveloping R`-linear map intertwines powers of `positiveAction`. -/
@[simp]
theorem map_positiveAction_pow (f : M →ₗ[Enveloping R] N) (i : I) (k : ℕ) (m : M) :
    f ((positiveAction R M i ^ k) m) = (positiveAction R N i ^ k) (f m) :=
  map_lieAction_pow f (positiveGenerator R i) k m

/-- Any `Enveloping R`-linear map intertwines powers of `negativeAction`. -/
@[simp]
theorem map_negativeAction_pow (f : M →ₗ[Enveloping R] N) (i : I) (k : ℕ) (m : M) :
    f ((negativeAction R M i ^ k) m) = (negativeAction R N i ^ k) (f m) :=
  map_lieAction_pow f (negativeGenerator R i) k m

end GeneratorActions

/-! ### Weight spaces and ladder shifts -/

section WeightSpaces

variable (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
variable (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
  [IsScalarTower K (Enveloping R) M]

/-- The **weight space** `M_μ` of an `Enveloping R`-module `M` for `μ ∈ Dual K H`, defined as the
joint eigenspace `⨅ x : H, (cartanAction R M x).eigenspace (μ x)`. -/
noncomputable def weightSpace (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] (μ : Dual K H) : Submodule K M :=
  ⨅ x : H, (cartanAction R M x).eigenspace (μ x)

theorem weightSpace_def (μ : Dual K H) :
    weightSpace R M μ = ⨅ x : H, (cartanAction R M x).eigenspace (μ x) := (rfl)

variable {R M}

theorem mem_weightSpace_iff {μ : Dual K H} {m : M} :
    m ∈ weightSpace R M μ ↔ ∀ x : H, cartanAction R M x m = μ x • m := by
  simp [weightSpace_def, Submodule.mem_iInf]

theorem cartanAction_apply_of_mem_weightSpace {μ : Dual K H} {m : M}
    (hm : m ∈ weightSpace R M μ) (x : H) :
    cartanAction R M x m = μ x • m :=
  mem_weightSpace_iff.mp hm x

theorem cartanAction_mem_weightSpace {μ : Dual K H} {m : M} (hm : m ∈ weightSpace R M μ) (x : H) :
    cartanAction R M x m ∈ weightSpace R M μ := by
  rw [cartanAction_apply_of_mem_weightSpace hm]
  exact (weightSpace R M μ).smul_mem (μ x) hm

/-- **Raising shifts weights by `+αᵢ`.** -/
theorem positiveAction_mem_weightSpace {μ : Dual K H} {m : M}
    (hm : m ∈ weightSpace R M μ) (i : I) :
    positiveAction R M i m ∈ weightSpace R M (μ + R.root i) := by
  rw [mem_weightSpace_iff]
  intro x
  rw [cartanAction_positiveAction_apply, cartanAction_apply_of_mem_weightSpace hm, map_smul,
    LinearMap.add_apply, add_smul]

/-- **Lowering shifts weights by `-αᵢ`.** -/
theorem negativeAction_mem_weightSpace {μ : Dual K H} {m : M}
    (hm : m ∈ weightSpace R M μ) (i : I) :
    negativeAction R M i m ∈ weightSpace R M (μ - R.root i) := by
  rw [mem_weightSpace_iff]
  intro x
  rw [cartanAction_negativeAction_apply, cartanAction_apply_of_mem_weightSpace hm, map_smul,
    LinearMap.sub_apply, sub_smul]

/-- Iterating `positiveAction R M i` `k` times shifts weights by `k • αᵢ`. -/
theorem positiveAction_pow_mem_weightSpace {μ : Dual K H} {m : M}
    (hm : m ∈ weightSpace R M μ) (i : I) (k : ℕ) :
    (positiveAction R M i ^ k) m ∈ weightSpace R M (μ + k • R.root i) := by
  induction k with
  | zero => simpa using hm
  | succ k ih =>
    rw [pow_succ', _root_.mul_apply_eq_comp, succ_nsmul, ← add_assoc]
    exact positiveAction_mem_weightSpace ih i

/-- Iterating `negativeAction R M i` `k` times shifts weights by `-k • αᵢ`. -/
theorem negativeAction_pow_mem_weightSpace {μ : Dual K H} {m : M}
    (hm : m ∈ weightSpace R M μ) (i : I) (k : ℕ) :
    (negativeAction R M i ^ k) m ∈ weightSpace R M (μ - k • R.root i) := by
  induction k with
  | zero => simpa using hm
  | succ k ih =>
    rw [pow_succ', _root_.mul_apply_eq_comp, succ_nsmul, sub_add_eq_sub_sub]
    exact negativeAction_mem_weightSpace ih i

variable (R M)

/-- Non-linear eigenvalue functions `H → K` have trivial joint eigenspaces, so the supremum of
`weightSpace R M μ` over `Dual K H` equals the supremum over all `χ : H → K`. -/
theorem iSup_weightSpace_eq_iSup_iInf_eigenspace :
    (⨆ μ : Dual K H, weightSpace R M μ) =
      ⨆ χ : H → K, ⨅ x : H, (cartanAction R M x).eigenspace (χ x) :=
  iSup_dual_eq_iSup (ρ := cartanAction R M)
    (fun χ ↦ ⨅ x : H, (cartanAction R M x).eigenspace (χ x)) fun _ ↦ le_rfl

/-- **Weight spaces for distinct weights are independent**, over any base field. -/
theorem iSupIndep_weightSpace : iSupIndep (weightSpace R M) :=
  (iSupIndep_iInf_eigenspace fun x : H ↦ cartanAction R M x).comp DFunLike.coe_injective

/-- If submodules `W j ≤ weightSpace R M (w j)` with pairwise distinct weights `w j` span `M`,
then each `weightSpace R M (w k)` equals `W k`. -/
theorem weightSpace_eq_of_iSup_eq_top {κ : Type*} {W : κ → Submodule K M} {w : κ → Dual K H}
    (hW : ∀ j, W j ≤ weightSpace R M (w j)) (htop : ⨆ j, W j = ⊤) (hw : Function.Injective w)
    (k : κ) :
    weightSpace R M (w k) = W k :=
  iInf_eigenspace_eq_of_iSup_eq_top (fun x : H ↦ cartanAction R M x) hW htop
    (DFunLike.coe_injective.comp hw) k

/-- If submodules `W j ≤ weightSpace R M (w j)` span `M`, then every weight outside the range of
`w` has zero weight space. -/
theorem weightSpace_eq_bot_of_iSup_eq_top {κ : Type*} {W : κ → Submodule K M} {w : κ → Dual K H}
    (hW : ∀ j, W j ≤ weightSpace R M (w j)) (htop : ⨆ j, W j = ⊤) {μ : Dual K H}
    (hμ : μ ∉ Set.range w) :
    weightSpace R M μ = ⊥ :=
  iInf_eigenspace_eq_bot_of_iSup_eq_top (fun x : H ↦ cartanAction R M x) hW htop
    fun ⟨j, hj⟩ ↦ hμ ⟨j, DFunLike.coe_injective hj⟩

variable {R M}
variable {N : Type*} [AddCommGroup N] [Module K N] [Module (Enveloping R) N]
  [IsScalarTower K (Enveloping R) N]

/-- Any `Enveloping R`-linear map carries `weightSpace R M μ` into `weightSpace R N μ`. -/
theorem map_weightSpace_le (f : M →ₗ[Enveloping R] N) (μ : Dual K H) :
    (weightSpace R M μ).map (f.restrictScalars K) ≤ weightSpace R N μ := by
  rintro _ ⟨m, hm, rfl⟩
  rw [mem_weightSpace_iff]
  intro x
  rw [LinearMap.coe_restrictScalars, ← map_cartanAction, cartanAction_apply_of_mem_weightSpace hm,
    ← LinearMap.coe_restrictScalars (R := K), map_smul]

theorem apply_mem_weightSpace_iff_of_injective {f : M →ₗ[Enveloping R] N}
    (hf : Function.Injective f) {μ : Dual K H} {m : M} :
    f m ∈ weightSpace R N μ ↔ m ∈ weightSpace R M μ := by
  refine ⟨fun h ↦ mem_weightSpace_iff.mpr fun x ↦ hf ?_, fun h ↦ map_weightSpace_le f μ ⟨m, h, rfl⟩⟩
  rw [map_cartanAction, cartanAction_apply_of_mem_weightSpace h,
    ← LinearMap.coe_restrictScalars (R := K) f, map_smul, LinearMap.coe_restrictScalars]

theorem weightSpace_eq_comap_of_injective {f : M →ₗ[Enveloping R] N} (hf : Function.Injective f)
    (μ : Dual K H) :
    weightSpace R M μ = (weightSpace R N μ).comap (f.restrictScalars K) := by
  ext m
  exact (apply_mem_weightSpace_iff_of_injective hf).symm

/-- The weight space of a product of `Enveloping R`-modules is the product of their weight
spaces. -/
@[simp]
theorem weightSpace_prod (μ : Dual K H) :
    weightSpace R (M × N) μ = (weightSpace R M μ).prod (weightSpace R N μ) := by
  ext ⟨m, n⟩
  simp [mem_weightSpace_iff, cartanAction_apply, Prod.ext_iff, forall_and]

section DirectSum

variable {κ : Type*} {P : κ → Type*} [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)]
  [∀ j, Module (Enveloping R) (P j)] [∀ j, IsScalarTower K (Enveloping R) (P j)]

theorem mem_weightSpace_directSum_iff {μ : Dual K H} {v : ⨁ j, P j} :
    v ∈ weightSpace R (⨁ j, P j) μ ↔ ∀ j, v j ∈ weightSpace R (P j) μ := by
  simp only [mem_weightSpace_iff]
  trans ∀ (x : H) (j : κ), (cartanAction R (⨁ j, P j) x v) j = (μ x • v) j
  · exact forall_congr' fun _ ↦ DFinsupp.ext_iff
  rw [forall_comm]
  refine forall_congr' fun j ↦ forall_congr' fun x ↦ ?_
  have h1 : (cartanAction R (⨁ j, P j) x v) j = cartanAction R (P j) x (v j) :=
    map_cartanAction (DirectSum.component (Enveloping R) κ P j) x v
  have h2 : (μ x • v) j = μ x • v j := (DirectSum.component K κ P j).map_smul (μ x) v
  rw [h1, h2]

private theorem weightSpace_directSum_eq_piSubmodule (μ : Dual K H) :
    weightSpace R (⨁ j, P j) μ =
      TauCeti.DirectSum.piSubmodule (fun j ↦ weightSpace R (P j) μ) := by
  ext v
  rw [mem_weightSpace_directSum_iff, TauCeti.DirectSum.mem_piSubmodule_iff]

/-- The `μ`-weight space of a direct sum `⨁ j, P j` is canonically `K`-linearly isomorphic to the
direct sum `⨁ j, weightSpace R (P j) μ`. -/
noncomputable def weightSpaceDirectSumEquiv (μ : Dual K H) :
    weightSpace R (⨁ j, P j) μ ≃ₗ[K] ⨁ j, weightSpace R (P j) μ :=
  (LinearEquiv.ofEq _ _ (weightSpace_directSum_eq_piSubmodule (R := R) (P := P) μ)).trans
    (TauCeti.DirectSum.piSubmoduleEquiv (fun j ↦ weightSpace R (P j) μ)).symm

/-- Componentwise evaluation of `weightSpaceDirectSumEquiv`. -/
@[simp]
theorem coe_weightSpaceDirectSumEquiv_apply (μ : Dual K H) (v : weightSpace R (⨁ j, P j) μ)
    (j : κ) :
    (weightSpaceDirectSumEquiv (R := R) (P := P) μ v j : P j) = (v : ⨁ j, P j) j := by
  simp [weightSpaceDirectSumEquiv]

/-- Componentwise evaluation of `(weightSpaceDirectSumEquiv μ).symm`. -/
@[simp]
theorem coe_weightSpaceDirectSumEquiv_symm_apply (μ : Dual K H)
    (w : ⨁ j, weightSpace R (P j) μ) (j : κ) :
    ((weightSpaceDirectSumEquiv (R := R) (P := P) μ).symm w : ⨁ j, P j) j = (w j : P j) := by
  simp [weightSpaceDirectSumEquiv]

/-- `(weightSpaceDirectSumEquiv μ).symm` sends `DirectSum.lof` on weight spaces to `DirectSum.lof`
on the ambient summands. -/
@[simp]
theorem coe_weightSpaceDirectSumEquiv_symm_lof [DecidableEq κ] (μ : Dual K H) (j : κ)
    (v : weightSpace R (P j) μ) :
    ((weightSpaceDirectSumEquiv (R := R) (P := P) μ).symm
        (DirectSum.lof K κ (fun j ↦ weightSpace R (P j) μ) j v) : ⨁ j, P j) =
      DirectSum.lof K κ P j v := by
  simp [weightSpaceDirectSumEquiv]

/-- `weightSpaceDirectSumEquiv` sends an ambient `DirectSum.lof` weight vector to `DirectSum.lof`
in the direct sum of weight spaces. -/
@[simp]
theorem weightSpaceDirectSumEquiv_lof [DecidableEq κ] (μ : Dual K H) (j : κ)
    (v : weightSpace R (P j) μ) :
    weightSpaceDirectSumEquiv (R := R) (P := P) μ
        ⟨DirectSum.lof K κ P j v, by
          rw [DirectSum.lof_eq_of K, ← DirectSum.lof_eq_of (Enveloping R)]
          exact map_weightSpace_le (DirectSum.lof (Enveloping R) κ P j) μ ⟨v, v.property, rfl⟩⟩ =
      DirectSum.lof K κ (fun j ↦ weightSpace R (P j) μ) j v := by
  apply (weightSpaceDirectSumEquiv (R := R) (P := P) μ).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  exact (coe_weightSpaceDirectSumEquiv_symm_lof (R := R) (P := P) μ j v).symm

theorem weightSpace_directSum_ne_bot_iff {μ : Dual K H} :
    weightSpace R (⨁ j, P j) μ ≠ ⊥ ↔ ∃ j, weightSpace R (P j) μ ≠ ⊥ := by
  classical
  constructor
  · intro h
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra! hall
      exact hv0 (DFinsupp.ext hall)
    exact ⟨j, (Submodule.ne_bot_iff _).mpr ⟨v j, mem_weightSpace_directSum_iff.mp hv j, hj⟩⟩
  · rintro ⟨j, hj⟩
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hj
    refine (Submodule.ne_bot_iff _).mpr ⟨DirectSum.lof (Enveloping R) κ P j m, ?_, ?_⟩
    · exact map_weightSpace_le (DirectSum.lof (Enveloping R) κ P j) μ ⟨m, hm, rfl⟩
    · intro h0
      exact hm0 (by simpa using congrArg (fun w : ⨁ j, P j ↦ w j) h0)

end DirectSum

end WeightSpaces

/-! ### Weight modules -/

section IsWeightModule

variable (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
variable (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
  [IsScalarTower K (Enveloping R) M]

/-- An `Enveloping R`-module `M` is a **weight module** when its weight spaces span `M`. -/
def IsWeightModule (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] : Prop :=
  ⨆ μ : Dual K H, weightSpace R M μ = ⊤

theorem isWeightModule_iff :
    IsWeightModule R M ↔ ⨆ μ : Dual K H, weightSpace R M μ = ⊤ := Iff.rfl

variable {R M}

theorem IsWeightModule.iSup_weightSpace_eq_top (hM : IsWeightModule R M) :
    ⨆ μ : Dual K H, weightSpace R M μ = ⊤ := hM

/-- A weight module is the internal direct sum of its weight spaces. -/
theorem IsWeightModule.isInternal [DecidableEq (Dual K H)] (hM : IsWeightModule R M) :
    DirectSum.IsInternal (weightSpace R M) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_weightSpace R M) hM

/-- Every `cartanAction`-invariant `K`-submodule of a weight module is the supremum of its
intersections with the weight spaces. -/
theorem IsWeightModule.iSup_inf_weightSpace_eq_of_forall_mapsTo (hM : IsWeightModule R M)
    (P : Submodule K M) (hP : ∀ x : H, Set.MapsTo (cartanAction R M x) P P) :
    (⨆ μ : Dual K H, P ⊓ weightSpace R M μ) = P := by
  have htop : (⨆ χ : H → K, ⨅ x : H, (cartanAction R M x).eigenspace (χ x)) = ⊤ := by
    rwa [← iSup_weightSpace_eq_iSup_iInf_eigenspace]
  have hle : P ≤ ⨆ χ : H → K, ⨅ x : H, (cartanAction R M x).eigenspace (χ x) := htop ▸ le_top
  simp_rw [weightSpace_def]
  rw [iSup_dual_eq_iSup (ρ := cartanAction R M)
    (fun χ ↦ P ⊓ ⨅ x : H, (cartanAction R M x).eigenspace (χ x)) fun _ ↦ inf_le_right]
  exact P.iSup_inf_iInf_eigenspace_eq_of_le hP hle

/-- Every `Enveloping R`-submodule of a weight module decomposes into weight components. -/
theorem IsWeightModule.iSup_inf_weightSpace_eq (hM : IsWeightModule R M)
    (P : Submodule (Enveloping R) M) :
    (⨆ μ : Dual K H, P.restrictScalars K ⊓ weightSpace R M μ) = P.restrictScalars K :=
  hM.iSup_inf_weightSpace_eq_of_forall_mapsTo (P.restrictScalars K) fun x _ hm ↦ by
    rw [Submodule.coe_restrictScalars, SetLike.mem_coe, cartanAction_apply]
    exact P.smul_mem (_root_.UniversalEnvelopingAlgebra.ι K (cartanElement R x)) hm

/-- Every nonzero `Enveloping R`-submodule of a weight module meets at least one weight space
nontrivially. -/
theorem IsWeightModule.exists_weightSpace_inf_ne_bot_of_ne_bot (hM : IsWeightModule R M)
    {P : Submodule (Enveloping R) M} (hP : P ≠ ⊥) :
    ∃ μ : Dual K H, P.restrictScalars K ⊓ weightSpace R M μ ≠ ⊥ := by
  by_contra! hall
  have hbot : P.restrictScalars K = ⊥ := by
    rw [← hM.iSup_inf_weightSpace_eq P]
    simp [hall]
  exact hP (Submodule.restrictScalars_injective K _ _ (by simpa using hbot))

section Closure

variable {N : Type*} [AddCommGroup N] [Module K N] [Module (Enveloping R) N]
  [IsScalarTower K (Enveloping R) N]

/-- Any module admitting an injective `Enveloping R`-linear map into a weight module is itself a
weight module. -/
theorem IsWeightModule.of_injective (hN : IsWeightModule R N) {f : M →ₗ[Enveloping R] N}
    (hf : Function.Injective f) : IsWeightModule R M := by
  rw [isWeightModule_iff, eq_top_iff]
  intro m _
  have hrange : ∀ x : H, Set.MapsTo (cartanAction R N x)
      (LinearMap.range (f.restrictScalars K)) (LinearMap.range (f.restrictScalars K)) := by
    rintro x _ ⟨y, rfl⟩
    exact ⟨cartanAction R M x y, map_cartanAction f x y⟩
  have hmem : f m ∈ ⨆ μ : Dual K H,
      LinearMap.range (f.restrictScalars K) ⊓ weightSpace R N μ := by
    rw [hN.iSup_inf_weightSpace_eq_of_forall_mapsTo _ hrange]
    exact ⟨m, rfl⟩
  have hsub : ⨆ μ : Dual K H, LinearMap.range (f.restrictScalars K) ⊓ weightSpace R N μ ≤
      (⨆ μ : Dual K H, weightSpace R M μ).map (f.restrictScalars K) := by
    refine iSup_le fun μ ↦ ?_
    rintro _ ⟨⟨y, rfl⟩, hy⟩
    exact Submodule.mem_map_of_mem
      (le_iSup (weightSpace R M) μ ((apply_mem_weightSpace_iff_of_injective hf).mp hy))
  obtain ⟨y, hy, hy_eq⟩ := hsub hmem
  exact hf hy_eq ▸ hy

/-- Every `Enveloping R`-submodule of a weight module is a weight module. -/
theorem IsWeightModule.submodule (hM : IsWeightModule R M) (P : Submodule (Enveloping R) M) :
    IsWeightModule R P :=
  hM.of_injective P.injective_subtype

/-- Surjective `Enveloping R`-linear maps from a weight module map each weight space onto the
corresponding weight space of the target. -/
theorem IsWeightModule.map_weightSpace_of_surjective (hM : IsWeightModule R M)
    {f : M →ₗ[Enveloping R] N} (hf : Function.Surjective f) (μ : Dual K H) :
    (weightSpace R M μ).map (f.restrictScalars K) = weightSpace R N μ := by
  have htop : (⨆ ν : Dual K H, (weightSpace R M ν).map (f.restrictScalars K)) = ⊤ := by
    rw [← Submodule.map_iSup, hM.iSup_weightSpace_eq_top, Submodule.map_top,
      LinearMap.range_eq_top]
    exact hf
  exact (weightSpace_eq_of_iSup_eq_top R N (fun ν ↦ map_weightSpace_le f ν) htop
    Function.injective_id μ).symm

/-- Surjective `Enveloping R`-linear images of weight modules are weight modules. -/
theorem IsWeightModule.of_surjective (hM : IsWeightModule R M) {f : M →ₗ[Enveloping R] N}
    (hf : Function.Surjective f) : IsWeightModule R N := by
  rw [isWeightModule_iff]
  simp_rw [← hM.map_weightSpace_of_surjective hf]
  rw [← Submodule.map_iSup, hM.iSup_weightSpace_eq_top, Submodule.map_top,
    LinearMap.range_eq_top]
  exact hf

/-- Quotients of weight modules are weight modules. -/
theorem IsWeightModule.quotient (hM : IsWeightModule R M) (P : Submodule (Enveloping R) M) :
    IsWeightModule R (M ⧸ P) :=
  hM.of_surjective P.mkQ_surjective

/-- Binary products of weight modules are weight modules. -/
theorem IsWeightModule.prod (hM : IsWeightModule R M) (hN : IsWeightModule R N) :
    IsWeightModule R (M × N) := by
  rw [isWeightModule_iff, eq_top_iff]
  rintro ⟨m, n⟩ _
  have hm : (m, (0 : N)) ∈ ⨆ μ : Dual K H, weightSpace R (M × N) μ := by
    have : m ∈ ⨆ μ : Dual K H, weightSpace R M μ := hM.symm ▸ Submodule.mem_top
    refine Submodule.iSup_induction (weightSpace R M) (motive := fun x ↦ (x, (0 : N)) ∈ _) this
      (fun μ x hx ↦ le_iSup (weightSpace R (M × N)) μ ?_) (zero_mem _) fun x y hx hy ↦ ?_
    · rw [weightSpace_prod]; exact ⟨hx, zero_mem _⟩
    · simpa [Prod.mk_add_mk] using add_mem hx hy
  have hn : ((0 : M), n) ∈ ⨆ μ : Dual K H, weightSpace R (M × N) μ := by
    have : n ∈ ⨆ μ : Dual K H, weightSpace R N μ := hN.symm ▸ Submodule.mem_top
    refine Submodule.iSup_induction (weightSpace R N) (motive := fun y ↦ ((0 : M), y) ∈ _) this
      (fun μ y hy ↦ le_iSup (weightSpace R (M × N)) μ ?_) (zero_mem _) fun x y hx hy ↦ ?_
    · rw [weightSpace_prod]; exact ⟨zero_mem _, hy⟩
    · simpa [Prod.mk_add_mk] using add_mem hx hy
  simpa using add_mem hm hn

/-- Direct sums of weight modules are weight modules. -/
theorem IsWeightModule.directSum {κ : Type*} {P : κ → Type*} [∀ j, AddCommGroup (P j)]
    [∀ j, Module K (P j)] [∀ j, Module (Enveloping R) (P j)]
    [∀ j, IsScalarTower K (Enveloping R) (P j)] (hP : ∀ j, IsWeightModule R (P j)) :
    IsWeightModule R (⨁ j, P j) := by
  classical
  rw [isWeightModule_iff, eq_top_iff]
  intro v _
  refine DirectSum.induction_on v (zero_mem _) (fun j m ↦ ?_) fun x y hx hy ↦ add_mem hx hy
  have hm : m ∈ ⨆ μ : Dual K H, weightSpace R (P j) μ := (hP j).symm ▸ Submodule.mem_top
  rw [← DirectSum.lof_eq_of (Enveloping R)]
  refine Submodule.iSup_induction (weightSpace R (P j))
    (motive := fun x ↦ DirectSum.lof (Enveloping R) κ P j x ∈ _) hm
    (fun μ x hx ↦ le_iSup (weightSpace R (⨁ j, P j)) μ
      (map_weightSpace_le (DirectSum.lof (Enveloping R) κ P j) μ ⟨x, hx, rfl⟩))
    (by rw [map_zero]; exact zero_mem _) fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy

end Closure

end IsWeightModule

/-! ### Category `O` and primitive vectors -/

section CategoryO

variable {R : CartanRealization (A.map (Int.cast : ℤ → K)) H}
variable {M : Type*} [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
  [IsScalarTower K (Enveloping R) M]

/-- Kac's **category `O`** (`IsCategoryO R M`): `M` is a weight module with finite-dimensional
weight spaces whose weights lie in finitely many cones `λ - Q₊`. -/
structure IsCategoryO (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Type*) [AddCommGroup M] [Module K M] [Module (Enveloping R) M]
    [IsScalarTower K (Enveloping R) M] : Prop where
  /-- `M` decomposes as a sum of weight spaces. -/
  isWeightModule : IsWeightModule R M
  /-- Every weight space of `M` is finite-dimensional over `K`. -/
  finiteDimensional_weightSpace : ∀ μ : Dual K H, FiniteDimensional K (weightSpace R M μ)
  /-- Finitely many weights bound all weights of `M` in `CartanRealization.RootLE`. -/
  exists_finset_rootLE :
    ∃ S : Finset (Dual K H), ∀ μ : Dual K H, weightSpace R M μ ≠ ⊥ → ∃ lam ∈ S, R.RootLE μ lam

variable {N : Type*} [AddCommGroup N] [Module K N] [Module (Enveloping R) N]
  [IsScalarTower K (Enveloping R) N]

/-- Category `O` is inherited along injective `Enveloping R`-linear maps. -/
theorem IsCategoryO.of_injective (hN : IsCategoryO R N) {f : M →ₗ[Enveloping R] N}
    (hf : Function.Injective f) : IsCategoryO R M where
  isWeightModule := hN.isWeightModule.of_injective hf
  finiteDimensional_weightSpace μ := by
    have := hN.finiteDimensional_weightSpace μ
    let g : weightSpace R M μ →ₗ[K] weightSpace R N μ :=
      { toFun := fun x ↦ ⟨f x.val, map_weightSpace_le f μ ⟨x.val, x.property, rfl⟩⟩
        map_add' := fun x y ↦ Subtype.ext (map_add f x.val y.val)
        map_smul' := fun c x ↦ Subtype.ext ((f.restrictScalars K).map_smul c x.val) }
    exact FiniteDimensional.of_injective g fun x y hxy ↦
      Subtype.ext (hf (congrArg Subtype.val hxy))
  exists_finset_rootLE := by
    obtain ⟨S, hS⟩ := hN.exists_finset_rootLE
    refine ⟨S, fun μ hμ ↦ hS μ ?_⟩
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
    exact (Submodule.ne_bot_iff _).mpr
      ⟨f m, map_weightSpace_le f μ ⟨m, hm, rfl⟩, fun h0 ↦ hm0 (hf (by simpa using h0))⟩

/-- Submodules of modules in `IsCategoryO` lie in `IsCategoryO`. -/
theorem IsCategoryO.submodule (hM : IsCategoryO R M) (P : Submodule (Enveloping R) M) :
    IsCategoryO R P :=
  hM.of_injective P.injective_subtype

/-- Surjective `Enveloping R`-linear images of modules in `IsCategoryO` lie in `IsCategoryO`. -/
theorem IsCategoryO.of_surjective (hM : IsCategoryO R M) {f : M →ₗ[Enveloping R] N}
    (hf : Function.Surjective f) : IsCategoryO R N where
  isWeightModule := hM.isWeightModule.of_surjective hf
  finiteDimensional_weightSpace μ := by
    have := hM.finiteDimensional_weightSpace μ
    rw [← hM.isWeightModule.map_weightSpace_of_surjective hf μ]
    infer_instance
  exists_finset_rootLE := by
    obtain ⟨S, hS⟩ := hM.exists_finset_rootLE
    refine ⟨S, fun μ hμ ↦ hS μ fun hbot ↦ hμ ?_⟩
    rw [← hM.isWeightModule.map_weightSpace_of_surjective hf μ, hbot, Submodule.map_bot]

/-- Quotients of modules in `IsCategoryO` lie in `IsCategoryO`. -/
theorem IsCategoryO.quotient (hM : IsCategoryO R M) (P : Submodule (Enveloping R) M) :
    IsCategoryO R (M ⧸ P) :=
  hM.of_surjective P.mkQ_surjective

/-- Binary products of modules in `IsCategoryO` lie in `IsCategoryO`. -/
theorem IsCategoryO.prod (hM : IsCategoryO R M) (hN : IsCategoryO R N) :
    IsCategoryO R (M × N) where
  isWeightModule := hM.isWeightModule.prod hN.isWeightModule
  finiteDimensional_weightSpace μ := by
    have := hM.finiteDimensional_weightSpace μ
    have := hN.finiteDimensional_weightSpace μ
    rw [weightSpace_prod]
    exact Module.Finite.equiv (Submodule.prodEquiv (weightSpace R M μ) (weightSpace R N μ)).symm
  exists_finset_rootLE := by
    classical
    obtain ⟨S₁, hS₁⟩ := hM.exists_finset_rootLE
    obtain ⟨S₂, hS₂⟩ := hN.exists_finset_rootLE
    refine ⟨S₁ ∪ S₂, fun μ hμ ↦ ?_⟩
    have hor : weightSpace R M μ ≠ ⊥ ∨ weightSpace R N μ ≠ ⊥ := by
      by_contra! hboth
      apply hμ
      rw [weightSpace_prod, hboth.left, hboth.right]
      ext ⟨x, y⟩
      simp
    rcases hor with h₁ | h₂
    · obtain ⟨lam, hlam, hle⟩ := hS₁ μ h₁
      exact ⟨lam, Finset.mem_union_left _ hlam, hle⟩
    · obtain ⟨lam, hlam, hle⟩ := hS₂ μ h₂
      exact ⟨lam, Finset.mem_union_right _ hlam, hle⟩

/-- Finite direct sums of modules in `IsCategoryO` lie in `IsCategoryO`. -/
theorem IsCategoryO.directSum {κ : Type*} [Finite κ] {P : κ → Type*}
    [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)] [∀ j, Module (Enveloping R) (P j)]
    [∀ j, IsScalarTower K (Enveloping R) (P j)] (hP : ∀ j, IsCategoryO R (P j)) :
    IsCategoryO R (⨁ j, P j) where
  isWeightModule := IsWeightModule.directSum fun j ↦ (hP j).isWeightModule
  finiteDimensional_weightSpace μ := by
    cases nonempty_fintype κ
    have : ∀ j, FiniteDimensional K (weightSpace R (P j) μ) :=
      fun j ↦ (hP j).finiteDimensional_weightSpace μ
    exact Module.Finite.equiv
      ((weightSpaceDirectSumEquiv (R := R) (P := P) μ).trans
        (DirectSum.linearEquivFunOnFintype K κ fun j ↦ weightSpace R (P j) μ)).symm
  exists_finset_rootLE := by
    classical
    cases nonempty_fintype κ
    choose S hS using fun j ↦ (hP j).exists_finset_rootLE
    refine ⟨Finset.univ.biUnion S, fun μ hμ ↦ ?_⟩
    obtain ⟨j, hj⟩ := weightSpace_directSum_ne_bot_iff.mp hμ
    obtain ⟨lam, hlam, hle⟩ := hS j μ hj
    exact ⟨lam, Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hlam⟩, hle⟩

section MaximalWeight

variable [CharZero K]

/-- **Existence of maximal weights under a finite upper-cone bound.** Over a field of characteristic
zero, if `M` is a weight module whose weights lie in finitely many cones `λ - Q₊`, then every
nonzero `Enveloping R`-submodule `P` of `M` admits a `RootLE`-maximal weight among the weights
meeting `P`. Neither finite-dimensionality of weight spaces nor finiteness of `I` is needed. -/
theorem IsWeightModule.exists_maximal_weight_of_exists_finset_rootLE
    (hM : IsWeightModule R M)
    (hS : ∃ S : Finset (Dual K H),
      ∀ μ : Dual K H, weightSpace R M μ ≠ ⊥ → ∃ lam ∈ S, R.RootLE μ lam)
    {P : Submodule (Enveloping R) M} (hP : P ≠ ⊥) :
    ∃ μ : Dual K H, P.restrictScalars K ⊓ weightSpace R M μ ≠ ⊥ ∧
      ∀ ν : Dual K H, P.restrictScalars K ⊓ weightSpace R M ν ≠ ⊥ → R.RootLE μ ν → ν = μ := by
  obtain ⟨S, hS⟩ := hS
  obtain ⟨μ₀, hμ₀⟩ := hM.exists_weightSpace_inf_ne_bot_of_ne_bot hP
  obtain ⟨μ, hμ, -, hmax⟩ := CartanRealization.exists_maximal_of_rootLE_finset
    (Q := fun ν ↦ P.restrictScalars K ⊓ weightSpace R M ν ≠ ⊥)
    (fun ν hν ↦ hS ν fun hbot ↦ hν (by simp [hbot])) hμ₀
  exact ⟨μ, hμ, hmax⟩

/-- **Existence of primitive vectors under a finite upper-cone bound.** Over a field of
characteristic zero, every nonzero `Enveloping R`-submodule `P` of a weight module whose weights lie
in finitely many cones `λ - Q₊` contains a nonzero weight vector annihilated by every
`positiveAction R M i`. -/
theorem IsWeightModule.exists_primitive_vector_of_exists_finset_rootLE
    (hM : IsWeightModule R M)
    (hS : ∃ S : Finset (Dual K H),
      ∀ μ : Dual K H, weightSpace R M μ ≠ ⊥ → ∃ lam ∈ S, R.RootLE μ lam)
    {P : Submodule (Enveloping R) M} (hP : P ≠ ⊥) :
    ∃ (μ : Dual K H) (v : M), v ∈ P ∧ v ≠ 0 ∧ v ∈ weightSpace R M μ ∧
      ∀ i : I, positiveAction R M i v = 0 := by
  obtain ⟨μ, hμ, hmax⟩ := hM.exists_maximal_weight_of_exists_finset_rootLE hS hP
  obtain ⟨v, ⟨hvP, hvw⟩, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  refine ⟨μ, v, hvP, hv0, hvw, fun i ↦ ?_⟩
  by_contra hne
  have heP : positiveAction R M i v ∈ P := by
    rw [positiveAction_apply]
    exact P.smul_mem (_root_.UniversalEnvelopingAlgebra.ι K (positiveGenerator R i)) hvP
  have heW : positiveAction R M i v ∈ weightSpace R M (μ + R.root i) :=
    positiveAction_mem_weightSpace hvw i
  have hinf : P.restrictScalars K ⊓ weightSpace R M (μ + R.root i) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨_, ⟨heP, heW⟩, hne⟩
  have hle : R.RootLE μ (μ + R.root i) := by
    simpa [CartanRealization.rootLE_iff] using R.root_mem_posRootCone i
  have hroot0 : R.root i = 0 := by
    simpa using hmax (μ + R.root i) hinf hle
  exact R.root_linearIndependent.ne_zero i hroot0

/-- **Existence of maximal weights in category `O`.** Over a field of characteristic zero, every
nonzero `Enveloping R`-submodule `P` of a module `M` in `IsCategoryO` admits a `RootLE`-maximal
weight meeting `P`. -/
theorem IsCategoryO.exists_maximal_weight_of_ne_bot (hM : IsCategoryO R M)
    {P : Submodule (Enveloping R) M} (hP : P ≠ ⊥) :
    ∃ μ : Dual K H, P.restrictScalars K ⊓ weightSpace R M μ ≠ ⊥ ∧
      ∀ ν : Dual K H, P.restrictScalars K ⊓ weightSpace R M ν ≠ ⊥ → R.RootLE μ ν → ν = μ :=
  hM.isWeightModule.exists_maximal_weight_of_exists_finset_rootLE hM.exists_finset_rootLE hP

/-- **Existence of primitive vectors in category `O`.** Over a field of characteristic zero, every
nonzero `Enveloping R`-submodule `P` of a module `M` in `IsCategoryO` contains a nonzero weight
vector annihilated by every `positiveAction R M i`. -/
theorem IsCategoryO.exists_primitive_vector_of_ne_bot (hM : IsCategoryO R M)
    {P : Submodule (Enveloping R) M} (hP : P ≠ ⊥) :
    ∃ (μ : Dual K H) (v : M), v ∈ P ∧ v ≠ 0 ∧ v ∈ weightSpace R M μ ∧
      ∀ i : I, positiveAction R M i v = 0 :=
  hM.isWeightModule.exists_primitive_vector_of_exists_finset_rootLE hM.exists_finset_rootLE hP

end MaximalWeight

end CategoryO

end KacMoody

end TauCeti
