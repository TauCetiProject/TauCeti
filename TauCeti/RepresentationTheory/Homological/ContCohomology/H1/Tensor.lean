/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Algebra.Module.ZMod.SMulCommClass
public import TauCeti.Data.ZMod.TrivialAction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.CoprimeDescent

/-!
# First cohomology tensor comparison and prime-to-index descent

Let `N` be an open normal subgroup of `G`, let `p` be prime to `[G : N]`, and let `A` be a
finite `ZMod p`-module with the discrete topology on which `N` acts trivially. This file
constructs the canonical comparison (available for any topological group acting trivially on a
discrete `A`)

```text
H¹(N, ZMod p) ⊗ A ≃ H¹(N, A).
```

The map evaluates a continuous character and scales its value by the tensor's second factor.
It intertwines inverse conjugation on `H¹(N, ZMod p)` and the coefficient action on `A` with
conjugation on `H¹(N, A)`. Restriction and the prime-to-`p` coprime-descent theorem therefore give

```text
dim H¹(G, A) = dim (H¹(N, ZMod p) ⊗ A)^G.
```

The final form is stated using the quotient representation of `G/N`, so it can be consumed by
representation-theoretic invariant-dimension results.

## Main definitions

* `TauCeti.h1TensorEquiv`: the canonical linear equivalence in first cohomology.
* `TauCeti.h1TensorConj`: the diagonal conjugation map on its source.
* `TauCeti.h1ConjRepresentation`: the induced `G/N`-representation on `H¹(N, ZMod p)`.
* `TauCeti.h1CoprimeTensorInvariantsEquiv`: coprime descent followed by the tensor comparison.

## Main results

* `TauCeti.h1TensorEquiv_conj`: the comparison is `G`-equivariant.
* `TauCeti.finrank_H1_eq_finrank_tensorInvariants`: the tensor-invariant dimension formula.
* `TauCeti.finrank_H1_eq_finrank_representationInvariants`: the same formula for the formal
  quotient representation.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of
  (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, I, proof of Theorem 2.8.
-/

public section

namespace TauCeti

open CategoryTheory ContCohomology
open scoped TensorProduct

universe uG uA

attribute [local instance] trivialZModAction

local instance continuousSMulTrivialZMod {n : ℕ} {H : Type*} [Monoid H]
    [TopologicalSpace H] : ContinuousSMul H (ZMod n) := ⟨continuous_snd⟩

section TrivialAction

variable {p : ℕ} {H : Type uG} [Group H] [TopologicalSpace H]
  {A : Type uA} [AddCommGroup A] [Module (ZMod p) A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [DistribMulAction H A] [ContinuousSMul H A]
  [DiscreteTopology A]

/-- **The first-cohomology tensor comparison.** If `H` acts trivially on a finite
`ZMod p`-module `A` with the discrete topology, evaluation identifies `H¹(H, ZMod p) ⊗ A` with
`H¹(H, A)`. The map is canonical even though a basis is used to prove its bijectivity. -/
noncomputable def h1TensorEquiv
    (htriv : ∀ (h : H) (a : A), h • a = a) [Fact p.Prime]
    [Module.Finite (ZMod p) A] :
    H1 H (ZMod p) ⊗[ZMod p] A ≃ₗ[ZMod p] H1 H A :=
  TensorProduct.congr
      (h1EquivContinuousZModDual (fun (_ : H) (_ : ZMod p) ↦ rfl))
      (LinearEquiv.refl _ A) ≪≫ₗ
    continuousZModDualTensorEquiv ≪≫ₗ
      (h1EquivContinuousZModHom htriv).symm

/-- On a pure tensor, `h1TensorEquiv` is pointwise evaluation followed by scalar multiplication. -/
@[simp]
theorem h1TensorEquiv_tmul_apply
    (htriv : ∀ (h : H) (a : A), h • a = a) [Fact p.Prime]
    [Module.Finite (ZMod p) A] (x : H1 H (ZMod p)) (a : A) (h : H) :
    Additive.toMul (H1EquivOfSmulEqSelf htriv (h1TensorEquiv htriv (x ⊗ₜ a))) h =
      Multiplicative.ofAdd
        (Multiplicative.toAdd (Additive.toMul (h1EquivContinuousZModDual
          (fun (_ : H) (_ : ZMod p) ↦ rfl) x) h) • a) := by
  simp only [h1TensorEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, continuousZModDualTensorEquiv_apply,
    H1EquivOfSmulEqSelf_h1EquivContinuousZModHom_symm_apply,
    continuousZModDualTensorMap_tmul_apply]

end TrivialAction

section TensorComparison

variable {p : ℕ} {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} [N.Normal]
  {A : Type uA} [AddCommGroup A] [Module (ZMod p) A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [DistribMulAction G A] [ContinuousSMul G A]
  [DiscreteTopology A]

omit [DiscreteTopology A] in
/-- Under the continuous-homomorphism description of `H¹`, conjugation sends a character `c`
to `n ↦ g • c(g⁻¹ng)`. -/
theorem H1EquivOfSmulEqSelf_explicitConj1_apply
    (hN : ∀ (n : N) (a : A), (n : G) • a = a)
    (g : G) (x : H1 N A) (n : N) :
    Additive.toMul (H1EquivOfSmulEqSelf hN (explicitConj1 N g x)) n =
      Multiplicative.ofAdd
        (g • Multiplicative.toAdd
          (Additive.toMul (H1EquivOfSmulEqSelf hN x)
            (Subgroup.inverseConjugationHom N g n))) := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
      rw [explicitConj1_apply_eq_smul, smul_mk, H1EquivOfSmulEqSelf_mk,
        H1EquivOfSmulEqSelf_mk, Z1EquivOfSmulEqSelf_apply,
        Z1EquivOfSmulEqSelf_apply, cocyclesMap1_apply,
        DistribSMul.toAddMonoidHom_apply]
      rfl

/-- The diagonal action on `H¹(N, ZMod p) ⊗ A`: conjugation on the character factor and the
given action on the coefficient factor. -/
noncomputable def h1TensorConj (g : G) :
    H1 N (ZMod p) ⊗[ZMod p] A →ₗ[ZMod p] H1 N (ZMod p) ⊗[ZMod p] A :=
  TensorProduct.map
    (AddMonoidHom.toZModLinearMap p (explicitConj1 (M := ZMod p) N g))
    (AddMonoidHom.toZModLinearMap p (DistribSMul.toAddMonoidHom A g))

omit [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul G A]
    [DiscreteTopology A] in
/-- The diagonal conjugation map acts on a pure tensor by conjugating the first factor and
applying the coefficient action to the second. -/
@[simp]
theorem h1TensorConj_tmul (g : G) (x : H1 N (ZMod p)) (a : A) :
    h1TensorConj g (x ⊗ₜ a) = explicitConj1 N g x ⊗ₜ (g • a) := by
  rw [h1TensorConj, TensorProduct.map_tmul, AddMonoidHom.coe_toZModLinearMap,
    AddMonoidHom.coe_toZModLinearMap, DistribSMul.toAddMonoidHom_apply]

/-- Equivariance of `h1TensorEquiv` on pure tensors. -/
theorem h1TensorEquiv_conj_tmul
    (hN : ∀ (n : N) (a : A), (n : G) • a = a) [Fact p.Prime]
    [Module.Finite (ZMod p) A] (g : G) (x : H1 N (ZMod p)) (a : A) :
    h1TensorEquiv hN (explicitConj1 N g x ⊗ₜ (g • a)) =
      explicitConj1 N g (h1TensorEquiv hN (x ⊗ₜ a)) := by
  apply (H1EquivOfSmulEqSelf hN).injective
  apply Additive.toMul.injective
  apply ContinuousMonoidHom.ext
  intro n
  rw [h1TensorEquiv_tmul_apply, H1EquivOfSmulEqSelf_explicitConj1_apply,
    h1TensorEquiv_tmul_apply]
  have hx : Multiplicative.toAdd
      (Additive.toMul (h1EquivContinuousZModDual (fun (_ : N) (_ : ZMod p) ↦ rfl)
        (explicitConj1 N g x)) n) =
      Multiplicative.toAdd
        (Additive.toMul (h1EquivContinuousZModDual (fun (_ : N) (_ : ZMod p) ↦ rfl) x)
          (Subgroup.inverseConjugationHom N g n)) := by
    have hx0 := H1EquivOfSmulEqSelf_explicitConj1_apply
      (G := G) (N := N) (A := ZMod p) (fun _ _ ↦ rfl) g x n
    have hx1 : Additive.toMul
        (h1EquivContinuousZModDual (fun (_ : N) (_ : ZMod p) ↦ rfl)
          (explicitConj1 N g x)) n =
      Additive.toMul
        (h1EquivContinuousZModDual (fun (_ : N) (_ : ZMod p) ↦ rfl) x)
          (Subgroup.inverseConjugationHom N g n) := by
      rw [h1EquivContinuousZModDual_apply, h1EquivContinuousZModDual_apply]
      exact hx0.trans (by rfl)
    exact congrArg Multiplicative.toAdd hx1
  rw [hx]
  simp only [toAdd_ofAdd]
  exact congrArg Multiplicative.ofAdd (smul_comm _ _ _)

/-- **The first-cohomology tensor comparison is equivariant** for the diagonal conjugation and
coefficient action. -/
theorem h1TensorEquiv_conj
    (hN : ∀ (n : N) (a : A), (n : G) • a = a) [Fact p.Prime]
    [Module.Finite (ZMod p) A] (g : G) (z : H1 N (ZMod p) ⊗[ZMod p] A) :
    h1TensorEquiv hN (h1TensorConj g z) = explicitConj1 N g (h1TensorEquiv hN z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x a => simpa only [h1TensorConj_tmul] using h1TensorEquiv_conj_tmul hN g x a

/-- The subspace fixed by every diagonal conjugation map on `H¹(N, ZMod p) ⊗ A`. When `N`
acts trivially on `A`, the diagonal action factors through `G/N`, and this is the invariant
subspace of the induced quotient representation. -/
def h1TensorConjInvariants : Submodule (ZMod p) (H1 N (ZMod p) ⊗[ZMod p] A) where
  carrier := {z | ∀ g : G, h1TensorConj g z = z}
  zero_mem' g := map_zero _
  add_mem' hx hy g := by rw [map_add, hx g, hy g]
  smul_mem' c z hz g := by rw [map_smul, hz g]

omit [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul G A]
    [DiscreteTopology A] in
/-- Membership in `h1TensorConjInvariants` means being fixed by every diagonal conjugation map. -/
@[simp]
theorem mem_h1TensorConjInvariants_iff {z : H1 N (ZMod p) ⊗[ZMod p] A} :
    z ∈ h1TensorConjInvariants (p := p) (G := G) (N := N) (A := A) ↔
      ∀ g : G, h1TensorConj g z = z :=
  Iff.rfl

/-- Equivariance restricts `h1TensorEquiv` to the invariant subspaces. -/
noncomputable def h1TensorInvariantsEquiv
    (hN : ∀ (n : N) (a : A), (n : G) • a = a) [Fact p.Prime]
    [Module.Finite (ZMod p) A] :
    h1TensorConjInvariants (p := p) (G := G) (N := N) (A := A) ≃ₗ[ZMod p]
      AddSubgroup.toZModSubmodule p (H1ConjInvariants G A N) where
  toFun z := ⟨h1TensorEquiv (p := p) hN z,
    (mem_H1ConjInvariants_iff G A N).2 fun g ↦ by
      rw [← h1TensorEquiv_conj (p := p) hN]
      exact congrArg (h1TensorEquiv (p := p) hN) (z.2 g)⟩
  invFun x := ⟨(h1TensorEquiv (p := p) hN).symm x, fun g ↦ by
    apply (h1TensorEquiv (p := p) hN).injective
    rw [h1TensorEquiv_conj (p := p), LinearEquiv.apply_symm_apply]
    exact (mem_H1ConjInvariants_iff G A N).1 x.2 g⟩
  left_inv z := Subtype.ext ((h1TensorEquiv (p := p) hN).symm_apply_apply z)
  right_inv x := Subtype.ext ((h1TensorEquiv (p := p) hN).apply_symm_apply x)
  map_add' x y := Subtype.ext (map_add (h1TensorEquiv (p := p) hN) x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul (h1TensorEquiv (p := p) hN) c x.1)

/-- The forward map of `h1TensorInvariantsEquiv` is `h1TensorEquiv` on underlying elements. -/
@[simp]
theorem h1TensorInvariantsEquiv_apply
    (hN : ∀ (n : N) (a : A), (n : G) • a = a) [Fact p.Prime]
    [Module.Finite (ZMod p) A]
    (z : h1TensorConjInvariants (p := p) (G := G) (N := N) (A := A)) :
    (h1TensorInvariantsEquiv hN z : H1 N A) =
      h1TensorEquiv hN (z : H1 N (ZMod p) ⊗[ZMod p] A) := by
  unfold h1TensorInvariantsEquiv
  rfl

/-- The inverse of `h1TensorInvariantsEquiv` is the inverse of `h1TensorEquiv` on underlying
elements. -/
@[simp]
theorem h1TensorInvariantsEquiv_symm_apply
    (hN : ∀ (n : N) (a : A), (n : G) • a = a) [Fact p.Prime]
    [Module.Finite (ZMod p) A]
    (x : AddSubgroup.toZModSubmodule p (H1ConjInvariants G A N)) :
    ((h1TensorInvariantsEquiv hN).symm x : H1 N (ZMod p) ⊗[ZMod p] A) =
      (h1TensorEquiv hN).symm x := by
  unfold h1TensorInvariantsEquiv
  rfl

/-- **Coprime descent followed by the tensor comparison.** -/
noncomputable def h1CoprimeTensorInvariantsEquiv
    (hN : ∀ (n : N) (a : A), (n : G) • a = a) [Fact p.Prime]
    [Module.Finite (ZMod p) A] [N.FiniteIndex] (hopen : IsOpen (N : Set G))
    (hcop : N.index.Coprime p) :
    H1 G A ≃ₗ[ZMod p]
      h1TensorConjInvariants (p := p) (G := G) (N := N) (A := A) :=
  h1CoprimeDescentEquiv hopen hcop ≪≫ₗ (h1TensorInvariantsEquiv hN).symm

/-- The forward map of `h1CoprimeTensorInvariantsEquiv` is restriction to `N` followed by the
inverse tensor comparison. -/
@[simp]
theorem h1CoprimeTensorInvariantsEquiv_apply
    (hN : ∀ (n : N) (a : A), (n : G) • a = a) [Fact p.Prime]
    [Module.Finite (ZMod p) A] [N.FiniteIndex] (hopen : IsOpen (N : Set G))
    (hcop : N.index.Coprime p) (x : H1 G A) :
    (h1CoprimeTensorInvariantsEquiv hN hopen hcop x : H1 N (ZMod p) ⊗[ZMod p] A) =
      (h1TensorEquiv hN).symm (explicitResConj1 G A N x : H1 N A) := by
  rw [h1CoprimeTensorInvariantsEquiv, LinearEquiv.trans_apply,
    h1TensorInvariantsEquiv_symm_apply, h1CoprimeDescentEquiv_apply]

/-- **The first-cohomology tensor-invariant dimension formula.** For an open normal subgroup of
index prime to `p` acting trivially on `A`, the dimension of `H¹(G, A)` is the dimension of the
invariants in `H¹(N, ZMod p) ⊗ A`. -/
theorem finrank_H1_eq_finrank_tensorInvariants
    (hN : ∀ (n : N) (a : A), (n : G) • a = a) [Fact p.Prime]
    [Module.Finite (ZMod p) A] [N.FiniteIndex] (hopen : IsOpen (N : Set G))
    (hcop : N.index.Coprime p) :
    Module.finrank (ZMod p) (H1 G A) =
      Module.finrank (ZMod p)
        (h1TensorConjInvariants (p := p) (G := G) (N := N) (A := A)) :=
  (h1CoprimeTensorInvariantsEquiv hN hopen hcop).finrank_eq

end TensorComparison

section QuotientRepresentation

variable {p : ℕ} {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} [N.Normal]

/-- Conjugation makes `H¹(N, ZMod p)` a `G/N`-representation. Inner conjugation by an element
of `N` is trivial on cohomology, so the ambient `G`-action factors through the quotient. -/
noncomputable def h1ConjRepresentation :
    Representation (ZMod p) (G ⧸ N) (H1 N (ZMod p)) := by
  let ρ : Representation (ZMod p) G (H1 N (ZMod p)) :=
    { toFun := fun g ↦ AddMonoidHom.toZModLinearMap p (explicitConj1 N g)
      map_one' := by
        apply LinearMap.ext
        intro x
        rw [AddMonoidHom.coe_toZModLinearMap, explicitConj1_one]
        rfl
      map_mul' := fun g h ↦ by
        apply LinearMap.ext
        intro x
        rw [AddMonoidHom.coe_toZModLinearMap, explicitConj1_mul]
        rfl }
  letI : Representation.IsTrivial (ρ.comp N.subtype) := ⟨fun n ↦ by
    apply LinearMap.ext
    intro x
    -- The local representation `ρ` has no separately named application lemma; reducing its
    -- composition with the subgroup inclusion exposes exactly the conjugation map defined above.
    change explicitConj1 N (n : G) x = x
    rw [explicitConj1_eq_id_of_mem]
    rfl⟩
  exact ρ.ofQuotient N

/-- The quotient representation evaluated on the class of `g` is conjugation by `g`. -/
@[simp]
theorem h1ConjRepresentation_quotient_mk_apply (g : G) (x : H1 N (ZMod p)) :
    h1ConjRepresentation (p := p) (G := G) (N := N) (g : G ⧸ N) x =
      explicitConj1 N g x := by
  rw [h1ConjRepresentation, Representation.ofQuotient_coe_apply]
  rfl

end QuotientRepresentation

section RepresentationInvariants

variable {p : ℕ} {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} [N.Normal]
  {A : Type uA} [AddCommGroup A] [Module (ZMod p) A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [DistribMulAction G A] [ContinuousSMul G A]
  [DiscreteTopology A]

omit [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul G A]
    [DiscreteTopology A] in
/-- The fixed subspace defined through `h1TensorConj` is the usual invariant subspace of the
tensor product of the quotient representations. -/
theorem h1TensorConjInvariants_eq_representationInvariants
    (ρ : Representation (ZMod p) (G ⧸ N) A)
    (hρ : ∀ (g : G) (a : A), ρ (g : G ⧸ N) a = g • a) :
    h1TensorConjInvariants (p := p) (G := G) (N := N) (A := A) =
      Representation.invariants ((h1ConjRepresentation (p := p) (G := G) (N := N)).tprod ρ) := by
  have hop (g : G) :
      (h1ConjRepresentation (p := p) (G := G) (N := N)).tprod ρ (g : G ⧸ N) =
        h1TensorConj (p := p) (N := N) (A := A) g := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x a =>
        rw [Representation.tprod_apply, TensorProduct.map_tmul, h1TensorConj,
          TensorProduct.map_tmul, AddMonoidHom.coe_toZModLinearMap,
          AddMonoidHom.coe_toZModLinearMap, h1ConjRepresentation_quotient_mk_apply, hρ]
        rfl
  ext z
  rw [mem_h1TensorConjInvariants_iff, Representation.mem_invariants]
  constructor
  · intro hz q
    induction q using QuotientGroup.induction_on with
    | H g => rw [hop g, hz g]
  · intro hz g
    rw [← hop g, hz (g : G ⧸ N)]

/-- **The representation-theoretic first-cohomology dimension formula.** This is the form
consumed by `finrankTensorInvariantsK0`: the right side is the invariant dimension of the tensor
of the quotient representation `H¹(N, ZMod p)` with `A`. -/
theorem finrank_H1_eq_finrank_representationInvariants
    (hN : ∀ (n : N) (a : A), (n : G) • a = a) [Fact p.Prime]
    [Module.Finite (ZMod p) A] [N.FiniteIndex] (hopen : IsOpen (N : Set G))
    (hcop : N.index.Coprime p) (ρ : Representation (ZMod p) (G ⧸ N) A)
    (hρ : ∀ (g : G) (a : A), ρ (g : G ⧸ N) a = g • a) :
    Module.finrank (ZMod p) (H1 G A) =
      Module.finrank (ZMod p) (Representation.invariants
        ((h1ConjRepresentation (p := p) (G := G) (N := N)).tprod ρ)) := by
  rw [finrank_H1_eq_finrank_tensorInvariants hN hopen hcop,
    h1TensorConjInvariants_eq_representationInvariants ρ hρ]

end RepresentationInvariants

end TauCeti
