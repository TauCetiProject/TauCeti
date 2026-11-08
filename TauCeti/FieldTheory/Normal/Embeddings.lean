/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.Algebra.GroupAction.AlgHom
public import TauCeti.GroupTheory.GroupAction.Transitive
import TauCeti.GroupTheory.Coset.Basic

/-!
# Embeddings into a normal extension, and the action on them

For fields `L` and `M` over a base `F`, the group `M ≃ₐ[F] M` acts on the embeddings
`L →ₐ[F] M` by postcomposition (`TauCeti/Algebra/GroupAction/AlgHom.lean`). This file records
the facts that make that action a dictionary for the subfields of `L`.

*Stabilizers.* The automorphisms fixing an embedding `φ` are exactly those fixing its image
`φ(L)` pointwise. Together with transitivity this identifies the coset space of
`Gal(M / φ(L))` with the set of all embeddings, the coset of `g` corresponding to `g ∘ φ`.

*Transitivity.* When `M / F` is normal, any two embeddings lie in the same orbit, because an
isomorphism between two embedded images extends to `M`. This asserts nothing about existence:
if no embedding `L →ₐ[F] M` exists the statement holds vacuously.

*Faithfulness.* When the embedded images generate `M` — that is, when
`IntermediateField.normalClosure F L M = ⊤` — an automorphism fixing every embedding is the
identity, so the action has trivial kernel.

*Counting.* When `L / F` is finite and separable, `M / F` is normal, and at least one embedding
`L →ₐ[F] M` exists, there are exactly `[L : F]` of them. All three hypotheses are needed: without
separability the count drops, and without normality the minimal polynomials need not split in `M`.

*Orbit maps.* If the subgroup fixing an intermediate field `K` fixes a point `x` of any
`Gal(M / F)`-set, an embedding of `K` into a normal `M` determines a point in the orbit of `x`.
This gives the surjection `G / Gal(M / K) → G / Stab(x)`, with fibres of cardinality
`[Stab(x) : Gal(M / K)]`. When `K / F` is separable, its degree is the orbit cardinality times
this relative index, so every finite separable field of definition bounds the orbit size.
The construction combines `fixingSubgroupQuotientEquivAlgHom` with Mathlib's
`MulAction.orbitEquivQuotientStabilizer` to identify embeddings and orbit points with cosets.

## Main results

* `AlgHom.liftNormal_equivFieldRange_apply`: lifting the isomorphism between two embedded
  images carries one embedding to the other. This isolates the field-range bookkeeping.
* `AlgEquiv.isPretransitiveAlgHom`: over a normal `M / F`, any two embeddings lie in one orbit.
* `TauCeti.FieldTheory.stabilizer_algHom_eq_fixingSubgroup`: the stabilizer of an embedding `φ`
  is the subgroup fixing `φ(L)`.
* `AlgHom.fixingSubgroup_fieldRange_conj`: the fixing subgroups of two embedded
  images are conjugate in a normal ambient extension.
* `TauCeti.FieldTheory.fixingSubgroupQuotientEquivAlgHom`: over a normal `M / F`, the cosets of
  that subgroup are the embeddings of `L` into `M`.
* `TauCeti.FieldTheory.eq_one_of_forall_smul_eq`: if the embedded images generate `M`, an
  automorphism fixing every embedding is the identity.
* `TauCeti.FieldTheory.faithfulSMul_of_normalClosure_eq_top`: equivalently, the action is
  faithful. Injectivity of the permutation representation is then Mathlib's
  `smul_left_injective'`.
* `TauCeti.FieldTheory.embeddingToOrbit`: embeddings of a field whose fixing subgroup fixes a point
  surject onto that point's orbit, with equivariance and a characteristic restriction equation.
* `TauCeti.FieldTheory.card_fiber_embeddingToOrbit`: each fibre has cardinality the relative
  index of the fixing subgroup in the stabilizer.
* `TauCeti.FieldTheory.finrank_eq_card_orbit_mul_relIndex`: for separable `K / F` in a normal
  ambient extension the field degree is the orbit cardinality times that relative index.
* `AlgHom.card_of_normal`: for `L / F` finite separable and `M / F` normal admitting an embedding
  of `L`, there are exactly `[L : F]` embeddings.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2 and §9.
-/

public section

open Polynomial IntermediateField

namespace AlgHom

variable {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]

/-- **Lifting the isomorphism between two embedded images carries one embedding to the other.**

This isolates the field-range and coercion bookkeeping: `φ x` is transported into `φ.fieldRange`,
the isomorphism `φ.fieldRange ≃ ψ.fieldRange` is applied there, and `liftNormal_commutes` brings
the result back to `M`. Keeping it separate lets `isPretransitiveAlgHom` state only the
mathematical step. -/
@[simp]
theorem liftNormal_equivFieldRange_apply [Normal F M] (φ ψ : L →ₐ[F] M) (x : L) :
    ((φ.equivFieldRange.symm.trans ψ.equivFieldRange).liftNormal M) (φ x) = ψ x := by
  simpa using
    (AlgEquiv.liftNormal_commutes (φ.equivFieldRange.symm.trans ψ.equivFieldRange) M
      (φ.equivFieldRange x))

end AlgHom

namespace AlgEquiv

variable {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]

/-- **Any two embeddings into a normal extension are conjugate**, so they lie in the same orbit.
No embedding is asserted to exist: when `L →ₐ[F] M` is empty this holds vacuously. -/
instance isPretransitiveAlgHom [Normal F M] :
    MulAction.IsPretransitive (M ≃ₐ[F] M) (L →ₐ[F] M) where
  -- Transport `φ`'s field range onto `ψ`'s, then lift that isomorphism to `M` by normality.
  exists_smul_eq φ ψ :=
    ⟨(φ.equivFieldRange.symm.trans ψ.equivFieldRange).liftNormal M, AlgHom.ext fun x => by
      rw [AlgEquiv.smul_algHom_apply]
      exact AlgHom.liftNormal_equivFieldRange_apply φ ψ x⟩

end AlgEquiv

namespace TauCeti.FieldTheory

variable {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]

/-- **An automorphism fixing every embedding is the identity**, provided the embedded images of
`L` generate `M`. -/
theorem eq_one_of_forall_smul_eq (hgen : IntermediateField.normalClosure F L M = ⊤)
    {σ : M ≃ₐ[F] M} (h : ∀ φ : L →ₐ[F] M, σ • φ = φ) : σ = 1 := by
  set H := Subgroup.closure ({σ} : Set (M ≃ₐ[F] M)) with hH
  have hfix : ∀ f : L →ₐ[F] M, f.fieldRange ≤ IntermediateField.fixedField H := by
    intro f
    have hσ : σ ∈ IntermediateField.fixingSubgroup f.fieldRange := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      rintro _ ⟨x, rfl⟩
      exact AlgEquiv.smul_algHom_eq_self_iff.1 (h f) x
    apply (IntermediateField.le_fixedField_iff_le_fixingSubgroup H f.fieldRange).2
    rw [hH, Subgroup.closure_le, Set.singleton_subset_iff]
    exact hσ
  have htop : (⊤ : IntermediateField F M) ≤ IntermediateField.fixedField H := by
    -- Unfold the normal closure to the supremum of the field ranges explicitly, rather than
    -- letting `iSup_le` match through the definition.
    rw [← hgen, normalClosure_def]
    exact iSup_le hfix
  rw [IntermediateField.le_fixedField_iff_le_fixingSubgroup, IntermediateField.fixingSubgroup_top,
    le_bot_iff] at htop
  have : σ ∈ (⊥ : Subgroup (M ≃ₐ[F] M)) := htop ▸ Subgroup.subset_closure rfl
  simpa using this

/-- **The action on embeddings is faithful** when the embedded images generate `M`.

With this instance in scope, injectivity of the permutation representation is Mathlib's
`smul_left_injective'`; no separate statement is needed. -/
theorem faithfulSMul_of_normalClosure_eq_top
    (hgen : IntermediateField.normalClosure F L M = ⊤) :
    FaithfulSMul (M ≃ₐ[F] M) (L →ₐ[F] M) :=
  faithfulSMul_iff.2 fun _ h => eq_one_of_forall_smul_eq hgen h

/-- **The stabilizer of an embedding is the subgroup fixing its image**: an automorphism of `M`
fixes `φ` under postcomposition exactly when it fixes `φ(L)` pointwise. No hypothesis on `M / F`
is needed. -/
theorem stabilizer_algHom_eq_fixingSubgroup (φ : L →ₐ[F] M) :
    MulAction.stabilizer (M ≃ₐ[F] M) φ = φ.fieldRange.fixingSubgroup := by
  ext g
  rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_algHom_eq_self_iff,
    IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h _ ⟨x, hx⟩ => hx ▸ h x, fun h x => h (φ x) ⟨x, rfl⟩⟩

end TauCeti.FieldTheory

namespace AlgHom

variable {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]

/-- The fixing subgroups of the images of two embeddings into a normal extension are
conjugate. No finiteness assumption on the embedded extension is needed. -/
theorem fixingSubgroup_fieldRange_conj [Normal F M] (φ ψ : L →ₐ[F] M) :
    ∃ g : M ≃ₐ[F] M,
      ψ.fieldRange.fixingSubgroup =
        φ.fieldRange.fixingSubgroup.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M ≃ₐ[F] M) φ ψ
  refine ⟨g, ?_⟩
  calc
    ψ.fieldRange.fixingSubgroup = MulAction.stabilizer (M ≃ₐ[F] M) ψ :=
      (TauCeti.FieldTheory.stabilizer_algHom_eq_fixingSubgroup ψ).symm
    _ = MulAction.stabilizer (M ≃ₐ[F] M) (g • φ) := by rw [hg]
    _ = (MulAction.stabilizer (M ≃ₐ[F] M) φ).map (MulAut.conj g).toMonoidHom :=
      MulAction.stabilizer_smul_eq_stabilizer_map_conj g φ
    _ = φ.fieldRange.fixingSubgroup.map (MulAut.conj g).toMonoidHom := by
      rw [TauCeti.FieldTheory.stabilizer_algHom_eq_fixingSubgroup]

end AlgHom

namespace TauCeti.FieldTheory

variable {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]

/-- **The cosets of `Gal(M / φ(L))` are the embeddings of `L` into `M`** for a normal `M / F`,
the coset of `g` corresponding to `g ∘ φ`. -/
noncomputable def fixingSubgroupQuotientEquivAlgHom [Normal F M] (φ : L →ₐ[F] M) :
    (M ≃ₐ[F] M) ⧸ φ.fieldRange.fixingSubgroup ≃ (L →ₐ[F] M) :=
  (Subgroup.quotientEquivOfEq (stabilizer_algHom_eq_fixingSubgroup φ).symm).trans
    (TauCeti.quotientStabilizerEquiv (M ≃ₐ[F] M) φ)

/-- `fixingSubgroupQuotientEquivAlgHom` sends the coset of `g` to `g ∘ φ`. -/
@[simp]
theorem fixingSubgroupQuotientEquivAlgHom_mk [Normal F M] (φ : L →ₐ[F] M) (g : M ≃ₐ[F] M) :
    fixingSubgroupQuotientEquivAlgHom φ (QuotientGroup.mk g) = g.toAlgHom.comp φ := by
  rw [fixingSubgroupQuotientEquivAlgHom, Equiv.trans_apply, Subgroup.quotientEquivOfEq_mk,
    TauCeti.quotientStabilizerEquiv_mk, AlgEquiv.smul_algHom_def]

section Orbit

variable {X : Type*} [MulAction (M ≃ₐ[F] M) X] {K : IntermediateField F M} {x : X}

/-- Identify the field range of the inclusion once for the quotient construction and its fibres. -/
private theorem fixingSubgroup_fieldRange_val_le
    (h : K.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[F] M) x) :
    K.val.fieldRange.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[F] M) x := by
  simpa only [IntermediateField.fieldRange_val] using h

/-- An embedding of `K` determines a point in the orbit of `x` whenever every automorphism
fixing `K` also fixes `x`. The restriction of `g` maps to `g • x`. -/
noncomputable def embeddingToOrbit [Normal F M]
    (h : K.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[F] M) x)
    (φ : K →ₐ[F] M) : MulAction.orbit (M ≃ₐ[F] M) x :=
  (MulAction.orbitEquivQuotientStabilizer (M ≃ₐ[F] M) x).symm
    (Subgroup.quotientMapOfLE (fixingSubgroup_fieldRange_val_le h)
      ((fixingSubgroupQuotientEquivAlgHom K.val).symm φ))

/-- The embedding obtained by restricting `g` maps to `g • x`. -/
@[simp]
theorem embeddingToOrbit_comp_val [Normal F M]
    (h : K.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[F] M) x) (g : M ≃ₐ[F] M) :
    (embeddingToOrbit h (g.toAlgHom.comp K.val) : X) = g • x := by
  rw [embeddingToOrbit, ← fixingSubgroupQuotientEquivAlgHom_mk K.val g,
    Equiv.symm_apply_apply, Subgroup.quotientMapOfLE_apply_mk,
    MulAction.orbitEquivQuotientStabilizer_symm_apply]

/-- Every point in the orbit is obtained from an embedding of `K`. -/
theorem embeddingToOrbit_surjective [Normal F M]
    (h : K.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[F] M) x) :
    Function.Surjective (embeddingToOrbit h) := by
  rintro ⟨y, g, rfl⟩
  exact ⟨g.toAlgHom.comp K.val, Subtype.ext (embeddingToOrbit_comp_val h g)⟩

/-- Postcomposition of embeddings corresponds to the action on the orbit. -/
theorem embeddingToOrbit_smul [Normal F M]
    (h : K.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[F] M) x)
    (g : M ≃ₐ[F] M) (φ : K →ₐ[F] M) :
    (embeddingToOrbit h (g • φ) : X) = g • (embeddingToOrbit h φ : X) := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq (M ≃ₐ[F] M) K.val φ
  rw [← mul_smul, AlgEquiv.smul_algHom_def, embeddingToOrbit_comp_val,
    AlgEquiv.smul_algHom_def, embeddingToOrbit_comp_val, mul_smul]

/-- Restrictions of two automorphisms give the same orbit point exactly when the automorphisms
have the same left coset of the stabilizer. -/
theorem embeddingToOrbit_eq_iff [Normal F M]
    (h : K.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[F] M) x) (g a : M ≃ₐ[F] M) :
    embeddingToOrbit h (g.toAlgHom.comp K.val) =
        embeddingToOrbit h (a.toAlgHom.comp K.val) ↔
      (QuotientGroup.mk g : (M ≃ₐ[F] M) ⧸ MulAction.stabilizer (M ≃ₐ[F] M) x) =
        QuotientGroup.mk a := by
  rw [Subtype.ext_iff, embeddingToOrbit_comp_val, embeddingToOrbit_comp_val,
    QuotientGroup.eq, MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
  exact eq_comm

/-- Every fibre has cardinality the relative index of the fixing subgroup in the stabilizer.
Infinite fibres have `Nat.card` zero, and neither subgroup needs to be normal. -/
theorem card_fiber_embeddingToOrbit [Normal F M]
    (h : K.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[F] M) x)
    (y : MulAction.orbit (M ≃ₐ[F] M) x) :
    Nat.card {φ : K →ₐ[F] M // embeddingToOrbit h φ = y} =
      K.fixingSubgroup.relIndex (MulAction.stabilizer (M ≃ₐ[F] M) x) := by
  let e := fixingSubgroupQuotientEquivAlgHom K.val
  let o := MulAction.orbitEquivQuotientStabilizer (M ≃ₐ[F] M) x
  have hf (φ) : embeddingToOrbit h φ = y ↔
      Subgroup.quotientMapOfLE (fixingSubgroup_fieldRange_val_le h) (e.symm φ) = o y := by
    simp only [embeddingToOrbit, e, Equiv.symm_apply_eq, o]
  rw [Nat.card_congr (e.symm.subtypeEquiv
      (q := fun q ↦ Subgroup.quotientMapOfLE (fixingSubgroup_fieldRange_val_le h) q = o y) hf),
    Subgroup.card_fiber_quotientMapOfLE, IntermediateField.fieldRange_val]

/-- For separable `K / F` in a normal ambient extension, the degree of `K` is the orbit
cardinality times the relative index of its fixing subgroup in the stabilizer. This natural-number
identity includes infinite degrees and orbits. Separability is essential to identify degree with
fixing-subgroup index; it is needed only for `K`, not for the ambient extension. -/
theorem finrank_eq_card_orbit_mul_relIndex [Normal F M] [Algebra.IsSeparable F K]
    (h : K.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[F] M) x) :
    Module.finrank F K = Nat.card (MulAction.orbit (M ≃ₐ[F] M) x) *
      K.fixingSubgroup.relIndex (MulAction.stabilizer (M ≃ₐ[F] M) x) := by
  let E := normalClosure F K M
  have hle : K ≤ E := by
    simpa only [fieldRange_val] using K.val.fieldRange_le_normalClosure
  let K' := restrict hle
  have hind : Module.finrank F K = K.fixingSubgroup.index := by
    rw [(restrictAlgEquiv hle).toLinearEquiv.finrank_eq,
      finrank_eq_fixingSubgroup_index, ← K'.map_fixingSubgroup_index M]
    congr 2
    exact lift_restrict hle
  rw [hind, Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm]
  exact (Subgroup.relIndex_mul_index h).symm

/-- The orbit cardinality divides the degree of every separable intermediate field whose fixing
subgroup fixes the point, in a normal ambient extension. -/
theorem card_orbit_dvd_finrank [Normal F M] [Algebra.IsSeparable F K]
    (h : K.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[F] M) x) :
    Nat.card (MulAction.orbit (M ≃ₐ[F] M) x) ∣ Module.finrank F K := by
  rw [finrank_eq_card_orbit_mul_relIndex h]
  exact dvd_mul_right _ _

/-- A finite separable intermediate field whose fixing subgroup fixes the point bounds the
orbit cardinality by its degree, in a normal ambient extension. -/
theorem card_orbit_le_finrank [Normal F M] [Algebra.IsSeparable F K] [FiniteDimensional F K]
    (h : K.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[F] M) x) :
    Nat.card (MulAction.orbit (M ≃ₐ[F] M) x) ≤ Module.finrank F K :=
  Nat.le_of_dvd Module.finrank_pos (card_orbit_dvd_finrank h)

end Orbit

end TauCeti.FieldTheory

namespace AlgHom

variable {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]

/-- **The number of embeddings is the degree.** For `L / F` finite and separable and `M / F`
normal, the existence of an embedding `L →ₐ[F] M` forces there to be exactly `[L : F]` of them:
every minimal polynomial over `F` of an element of `L` splits in `M`. -/
@[simp]
theorem card_of_normal [FiniteDimensional F L] [Algebra.IsSeparable F L] [Normal F M]
    [Nonempty (L →ₐ[F] M)] : Fintype.card (L →ₐ[F] M) = Module.finrank F L := by
  let φ := Classical.choice (inferInstance : Nonempty (L →ₐ[F] M))
  refine AlgHom.card_of_splits F L M ?_
  intro x
  -- An embedding preserves minimal polynomials, and `M / F` is normal.
  have h : minpoly F (φ x) = minpoly F x := minpoly.algHom_eq φ φ.injective x
  rw [← h]
  exact Normal.splits inferInstance (φ x)

end AlgHom

end
