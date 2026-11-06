/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.GroupAction.Transitive
public import TauCeti.Topology.Algebra.GroupAction.Discrete

/-!
# Labelled finite Galois sets

`TauCeti.GaloisSet K n` is an action of the Galois group of `SeparableClosure K` on
`Fin n`, specified by a permutation representation with open kernel. The labels retain
the multiplicities needed when counting étale algebras by their Galois actions.

The stabilizer of each point is open, its fixed field is finite over `K`, and its degree
is the orbit size. In particular, a nonempty labelled action is transitive exactly when
the fixed field of a point stabilizer has degree `n`. These results use Mathlib's infinite
Galois correspondence and orbit–stabilizer theorem. The conversion from continuous finite
actions uses `TauCeti.isOpen_ker_toPermHom`.

Only a field structure on `K` is needed here; valuations enter when assigning discriminant
weights to these actions.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density
  of number field discriminants*, IMRN 2007, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN 2007, rnm021.
-/

public section

noncomputable section

namespace TauCeti

universe u

/-- A labelled Galois set of size `n` is a permutation representation of the Galois group
of the separable closure with open kernel in the Krull topology. -/
abbrev GaloisSet (K : Type u) [Field K] (n : ℕ) : Type u :=
  {ρ : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →* Equiv.Perm (Fin n) //
    IsOpen (ρ.ker : Set (SeparableClosure K ≃ₐ[K] SeparableClosure K))}

namespace GaloisSet

variable {K : Type u} [Field K] {n : ℕ}

/-- Labelled Galois sets agree if their permutations agree at every group element and label. -/
@[ext]
theorem ext {ρ τ : GaloisSet K n}
    (h : ∀ σ i, ρ.val σ i = τ.val σ i) : ρ = τ :=
  Subtype.ext <| MonoidHom.ext fun σ ↦ Equiv.ext (h σ)

/-- The action associated to a labelled Galois set. Install it locally with
`letI := ρ.mulAction` to use the group-action API. -/
abbrev mulAction (ρ : GaloisSet K n) :
    MulAction (SeparableClosure K ≃ₐ[K] SeparableClosure K) (Fin n) :=
  MulAction.compHom (Fin n) ρ.val

/-- The associated action evaluates the permutation representation. -/
@[simp]
theorem smul_def (ρ : GaloisSet K n) (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (i : Fin n) : letI := ρ.mulAction; σ • i = ρ.val σ i :=
  (rfl)

/-- Point stabilizers are open because they contain the open kernel. -/
theorem isOpen_stabilizer (ρ : GaloisSet K n) (i : Fin n) :
    letI := ρ.mulAction
    IsOpen (MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i :
      Set (SeparableClosure K ≃ₐ[K] SeparableClosure K)) := by
  let := ρ.mulAction
  exact Subgroup.isOpen_mono (H₁ := ρ.val.ker)
    (fun σ hσ ↦ by simp [MulAction.mem_stabilizer_iff, MonoidHom.mem_ker.mp hσ]) ρ.property

/-- The open-kernel condition makes the action on the discrete set of labels continuous. -/
theorem continuousSMul (ρ : GaloisSet K n) :
    letI := ρ.mulAction
    ContinuousSMul (SeparableClosure K ≃ₐ[K] SeparableClosure K) (Fin n) := by
  let := ρ.mulAction
  exact continuousSMul_iff_stabilizer_isOpen.mpr ρ.isOpen_stabilizer

/-- Construct a labelled Galois set from a continuous action on `Fin n` with its discrete
topology. -/
def ofMulAction [MulAction (SeparableClosure K ≃ₐ[K] SeparableClosure K) (Fin n)]
    [ContinuousSMul (SeparableClosure K ≃ₐ[K] SeparableClosure K) (Fin n)] :
    GaloisSet K n :=
  ⟨MulAction.toPermHom _ _, isOpen_ker_toPermHom _ _⟩

/-- The permutation of the Galois set constructed from an action is its original action. -/
@[simp]
theorem ofMulAction_val_apply
    [MulAction (SeparableClosure K ≃ₐ[K] SeparableClosure K) (Fin n)]
    [ContinuousSMul (SeparableClosure K ≃ₐ[K] SeparableClosure K) (Fin n)]
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (i : Fin n) :
    (ofMulAction (K := K) (n := n)).val σ i = σ • i :=
  (rfl)

/-- Recovering the permutation representation from the associated action recovers the
labelled Galois set. -/
@[simp]
theorem ofMulAction_mulAction (ρ : GaloisSet K n) :
    letI := ρ.mulAction
    letI := ρ.continuousSMul
    ofMulAction (K := K) (n := n) = ρ := by
  apply ext
  intro σ i
  rfl

/-- The stabilizer is recovered from its fixed field by the infinite Galois correspondence. -/
@[simp]
theorem fixingSubgroup_fixedField_stabilizer (ρ : GaloisSet K n) (i : Fin n) :
    letI := ρ.mulAction
    (IntermediateField.fixedField
      (MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i)).fixingSubgroup =
      MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i := by
  let := ρ.mulAction
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨_, Subgroup.isClosed_of_isOpen _ (ρ.isOpen_stabilizer i)⟩

/-- The field fixed by a point stabilizer is a finite extension of `K`. -/
theorem finiteDimensional_fixedField_stabilizer (ρ : GaloisSet K n) (i : Fin n) :
    letI := ρ.mulAction
    FiniteDimensional K (IntermediateField.fixedField
      (MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i)) := by
  let := ρ.mulAction
  rw [← InfiniteGalois.isOpen_iff_finite, ρ.fixingSubgroup_fixedField_stabilizer]
  exact ρ.isOpen_stabilizer i

/-- The degree of the fixed field of a point stabilizer is the size of its orbit. -/
theorem finrank_fixedField_stabilizer (ρ : GaloisSet K n) (i : Fin n) :
    letI := ρ.mulAction
    Module.finrank K (IntermediateField.fixedField
      (MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i)) =
      Nat.card (MulAction.orbit (SeparableClosure K ≃ₐ[K] SeparableClosure K) i) := by
  let := ρ.mulAction
  rw [IntermediateField.finrank_eq_fixingSubgroup_index,
    ρ.fixingSubgroup_fixedField_stabilizer, MulAction.index_stabilizer, Nat.card_coe_set_eq]

/-- Transitivity of a labelled Galois set means pretransitivity of its associated action.
As with `MulAction.IsPretransitive`, this holds vacuously for the empty set. -/
def IsTransitive (ρ : GaloisSet K n) : Prop :=
  letI := ρ.mulAction
  MulAction.IsPretransitive (SeparableClosure K ≃ₐ[K] SeparableClosure K) (Fin n)

/-- Transitivity means that some group element takes any chosen label to any other label. -/
theorem isTransitive_iff (ρ : GaloisSet K n) :
    ρ.IsTransitive ↔ ∀ i j : Fin n,
      ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, ρ.val σ i = j := by
  let := ρ.mulAction
  exact MulAction.isPretransitive_iff _ _

/-- A transitive Galois set has a degree-`n` fixed field at every point stabilizer. -/
theorem finrank_fixedField_stabilizer_of_isTransitive (ρ : GaloisSet K n)
    (hρ : ρ.IsTransitive) (i : Fin n) :
    letI := ρ.mulAction
    Module.finrank K (IntermediateField.fixedField
      (MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i)) = n := by
  let := ρ.mulAction
  have : MulAction.IsPretransitive (SeparableClosure K ≃ₐ[K] SeparableClosure K) (Fin n) := hρ
  rw [ρ.finrank_fixedField_stabilizer, MulAction.orbit_eq_univ]
  simp

/-- On a nonempty labelled Galois set, transitivity is detected by the degree of the
fixed field of any one point stabilizer. -/
theorem isTransitive_iff_finrank_fixedField_stabilizer (ρ : GaloisSet K n) (i : Fin n) :
    ρ.IsTransitive ↔
      letI := ρ.mulAction
      Module.finrank K (IntermediateField.fixedField
        (MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i)) = n := by
  let := ρ.mulAction
  rw [IsTransitive, MulAction.isPretransitive_iff_orbit_eq_univ i, Set.eq_univ_iff_ncard,
    ρ.finrank_fixedField_stabilizer, ← Nat.card_coe_set_eq]
  simp

/-- The trivial action, with every label fixed. -/
def trivial (K : Type u) [Field K] (n : ℕ) : GaloisSet K n :=
  ⟨1, by simp⟩

instance : Inhabited (GaloisSet K n) := ⟨trivial K n⟩

/-- Every group element fixes every label of the trivial Galois set. -/
@[simp]
theorem trivial_val_apply (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (i : Fin n) :
    (trivial K n).val σ i = i :=
  (rfl)

instance [Subsingleton (Fin n)] : Subsingleton (GaloisSet K n) :=
  ⟨fun _ _ ↦ ext fun _ _ ↦ Subsingleton.elim _ _⟩

/-- There is exactly one labelled Galois set of size zero or one. -/
instance [Subsingleton (Fin n)] : Unique (GaloisSet K n) where
  default := trivial K n
  uniq _ := Subsingleton.elim _ _

/-- A point stabilizer in the trivial action fixes precisely the base field. -/
@[simp]
theorem fixedField_stabilizer_trivial (i : Fin n) :
    letI := (trivial K n).mulAction
    IntermediateField.fixedField
      (MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i) = ⊥ := by
  let := (trivial K n).mulAction
  have hstab : MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i = ⊤ := by
    ext σ
    simp [MulAction.mem_stabilizer_iff]
  rw [hstab, InfiniteGalois.fixedField_bot]

end GaloisSet

end TauCeti
