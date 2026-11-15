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
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import TauCeti.Logic.Equiv.Option

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

Conversely, an open subgroup `H` of index `n` and a labelling `Fin n ≃ G ⧸ H` of its cosets
give a transitive Galois set (`TauCeti.GaloisSet.ofQuotient`). For a subextension `L` of degree
`n` and a label `i`, the transitive Galois sets in which `i` has stabilizer fixed field `L` are
the labellings sending `i` to the trivial coset of the fixing subgroup of `L`, so there are
`(n - 1)!` of them (`TauCeti.GaloisSet.natCard_isTransitive_fixedField_stabilizer_eq`). Summing
over `L`, any weight of the fixed field of `i`, summed over transitive Galois sets of size `n`, is
`(n - 1)!` times its sum over the subextensions of degree `n`
(`TauCeti.GaloisSet.tsum_isTransitive`).

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

/-- Transitivity of a labelled Galois set is pretransitivity of its associated action. -/
theorem isTransitive_def (ρ : GaloisSet K n) :
    ρ.IsTransitive ↔
      letI := ρ.mulAction
      MulAction.IsPretransitive (SeparableClosure K ≃ₐ[K] SeparableClosure K) (Fin n) :=
  Iff.rfl

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

/-! ### Transitive Galois sets from open subgroups -/

/-- The labelled Galois set given by the coset action on `G ⧸ H` for an open subgroup `H`,
transported to `Fin n` along a labelling `e` of the cosets. -/
def ofQuotient (H : Subgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K))
    (hH : IsOpen (H : Set (SeparableClosure K ≃ₐ[K] SeparableClosure K)))
    (e : Fin n ≃ (SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ H) : GaloisSet K n :=
  ⟨e.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom _ _), by
    have : DiscreteTopology ((SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ H) :=
      QuotientGroup.discreteTopology hH
    have : Finite ((SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ H) := Finite.of_equiv _ e
    refine Subgroup.isOpen_mono (fun σ hσ ↦ ?_)
      (isOpen_ker_toPermHom (SeparableClosure K ≃ₐ[K] SeparableClosure K)
        ((SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ H))
    rw [MonoidHom.mem_ker] at hσ ⊢
    rw [MonoidHom.comp_apply, hσ, map_one]⟩

section ofQuotient

variable {H : Subgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K)}
  (hH : IsOpen (H : Set (SeparableClosure K ≃ₐ[K] SeparableClosure K)))

/-- The permutation of a label is the coset action transported along the labelling. -/
@[simp]
theorem ofQuotient_val_apply (e : Fin n ≃ (SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ H)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (i : Fin n) :
    (ofQuotient H hH e).val σ i = e.symm (σ • e i) :=
  (rfl)

/-- A labelled coset space is transitive. -/
theorem isTransitive_ofQuotient (e : Fin n ≃ (SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ H) :
    (ofQuotient H hH e).IsTransitive := by
  rw [isTransitive_iff]
  intro i j
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (e i) (e j)
  exact ⟨σ, by rw [ofQuotient_val_apply, hσ, Equiv.symm_apply_apply]⟩

/-- The label of the trivial coset has stabilizer `H`. -/
theorem stabilizer_ofQuotient (e : Fin n ≃ (SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ H)
    {i : Fin n} (hi : e i = ((1 : SeparableClosure K ≃ₐ[K] SeparableClosure K) : _ ⧸ H)) :
    letI := (ofQuotient H hH e).mulAction
    MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i = H := by
  let := (ofQuotient H hH e).mulAction
  ext σ
  rw [MulAction.mem_stabilizer_iff, smul_def, ofQuotient_val_apply, Equiv.symm_apply_eq, hi,
    ← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]

include hH in
/-- For an open subgroup `H` with `n` cosets, exactly `(n - 1)!` labelled Galois sets of size `n`
are transitive with stabilizer `H` at a given label `i`: they are the labellings of the cosets
sending `i` to the trivial coset. -/
theorem natCard_isTransitive_stabilizer_eq
    (hn : Nat.card ((SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ H) = n) (i : Fin n) :
    Nat.card {ρ : GaloisSet K n // ρ.IsTransitive ∧
      letI := ρ.mulAction
      MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i = H} =
      (n - 1).factorial := by
  let F : {e : Fin n ≃ (SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸ H //
      e i = ((1 : SeparableClosure K ≃ₐ[K] SeparableClosure K) : _ ⧸ H)} →
      {ρ : GaloisSet K n // ρ.IsTransitive ∧
        letI := ρ.mulAction
        MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i = H} :=
    fun e ↦ ⟨ofQuotient H hH e.1, isTransitive_ofQuotient hH e.1, stabilizer_ofQuotient hH e.1 e.2⟩
  have hF : Function.Bijective F := by
    constructor
    · -- Both labellings send `i` to the trivial coset, so the coset `σ H` labelled `j` by the
      -- first is `σ • i = j` for the second as well.
      intro e₁ e₂ h
      refine Subtype.ext (Equiv.ext fun j ↦ ?_)
      obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (e₁.1 j)
      have h' : e₁.1.symm (σ • e₁.1 i) = e₂.1.symm (σ • e₂.1 i) :=
        congrArg (fun ρ : {ρ : GaloisSet K n // _} ↦ ρ.1.val σ i) h
      rw [e₁.2, e₂.2, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hσ,
        Equiv.symm_apply_apply, Equiv.eq_symm_apply] at h'
      exact h'.symm
    · -- A transitive action is labelled by the orbit map of `i` on the cosets of its stabilizer.
      rintro ⟨ρ, hρ, hstab⟩
      let := ρ.mulAction
      have : MulAction.IsPretransitive (SeparableClosure K ≃ₐ[K] SeparableClosure K) (Fin n) := hρ
      subst hstab
      let e : (SeparableClosure K ≃ₐ[K] SeparableClosure K) ⧸
          MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i ≃ Fin n :=
        Equiv.ofBijective (MulAction.ofQuotientStabilizer _ i)
          ⟨MulAction.injective_ofQuotientStabilizer _ i, fun j ↦
            let ⟨σ, hσ⟩ :=
              MulAction.exists_smul_eq (SeparableClosure K ≃ₐ[K] SeparableClosure K) i j
            ⟨σ, hσ⟩⟩
      refine ⟨⟨e.symm, (e.symm_apply_eq).2
        (one_smul (SeparableClosure K ≃ₐ[K] SeparableClosure K) i).symm⟩,
        Subtype.ext (ext fun σ j ↦ ?_)⟩
      -- `e` is `Equiv.ofBijective` of the orbit map, which commutes with the action.
      change MulAction.ofQuotientStabilizer _ i (σ • e.symm j) = ρ.val σ j
      rw [MulAction.ofQuotientStabilizer_smul, ← smul_def]
      exact congrArg (σ • ·) (e.apply_symm_apply j)
  rw [← Nat.card_eq_of_bijective F hF,
    Nat.card_subtype_equiv_apply_eq ((Nat.card_fin n).trans hn.symm), Nat.card_fin]

end ofQuotient

/-- For a subextension `L` of degree `n`, exactly `(n - 1)!` labelled Galois sets of size `n` are
transitive with `L` as the fixed field of the stabilizer of a given label. -/
theorem natCard_isTransitive_fixedField_stabilizer_eq
    (L : IntermediateField K (SeparableClosure K)) (hL : Module.finrank K L = n) (i : Fin n) :
    Nat.card {ρ : GaloisSet K n // ρ.IsTransitive ∧
      letI := ρ.mulAction
      IntermediateField.fixedField
        (MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i) = L} =
      (n - 1).factorial := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (hL ▸ i.pos)
  rw [← natCard_isTransitive_stabilizer_eq L.fixingSubgroup_isOpen
    (by rw [← Subgroup.index, ← IntermediateField.finrank_eq_fixingSubgroup_index, hL]) i]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun ρ ↦ and_congr_right fun _ ↦ ?_)
  let := ρ.mulAction
  constructor
  · rintro h
    rw [← h, ρ.fixingSubgroup_fixedField_stabilizer]
  · rintro h
    rw [h, InfiniteGalois.fixedField_fixingSubgroup]

open scoped ENNReal in
/-- **Transitive Galois sets and subextensions.** Summed over the transitive labelled Galois sets
of size `n`, any weight `g` of the fixed field of the stabilizer of a label `i` is `(n - 1)!`
times the sum of `g` over the subextensions of `SeparableClosure K` of degree `n`: each such
subextension is the fixed field for exactly `(n - 1)!` of them. -/
theorem tsum_isTransitive (i : Fin n) (g : IntermediateField K (SeparableClosure K) → ℝ≥0∞) :
    ∑' ρ : {ρ : GaloisSet K n // ρ.IsTransitive},
        (letI := ρ.1.mulAction
        g (IntermediateField.fixedField
          (MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i))) =
      ((n - 1).factorial : ℝ≥0∞) *
        ∑' L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = n}, g L.1 := by
  let Φ : {ρ : GaloisSet K n // ρ.IsTransitive} →
      {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = n} := fun ρ ↦
    letI := ρ.1.mulAction
    ⟨IntermediateField.fixedField
      (MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i),
      ρ.1.finrank_fixedField_stabilizer_of_isTransitive ρ.2 i⟩
  rw [← tsum_fiberwise _ Φ, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun L ↦ ?_
  have hfib : ∀ ρ : Φ ⁻¹' {L}, (letI := ρ.1.1.mulAction
      g (IntermediateField.fixedField
        (MulAction.stabilizer (SeparableClosure K ≃ₐ[K] SeparableClosure K) i))) = g L.1 :=
    fun ρ ↦ congrArg (fun L : {L : IntermediateField K (SeparableClosure K) //
      Module.finrank K L = n} ↦ g L.1) ρ.2
  rw [tsum_congr hfib, ENNReal.tsum_const]
  have hcard : Nat.card (Φ ⁻¹' {L}) = (n - 1).factorial := by
    rw [← natCard_isTransitive_fixedField_stabilizer_eq L.1 L.2 i]
    exact Nat.card_congr
      { toFun := fun ρ ↦ ⟨ρ.1.1, ρ.1.2, congrArg Subtype.val ρ.2⟩
        invFun := fun ρ ↦ ⟨⟨ρ.1, ρ.2.1⟩, Subtype.ext ρ.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  have : Finite (Φ ⁻¹' {L}) := Nat.finite_of_card_ne_zero (hcard ▸ (n - 1).factorial_ne_zero)
  rw [ENat.card_eq_coe_natCard, hcard, ENat.toENNReal_coe]

end GaloisSet

end TauCeti
