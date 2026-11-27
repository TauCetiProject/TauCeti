/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Decomposition
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations
import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Transitivity
import TauCeti.RepresentationTheory.BaseChange
import TauCeti.RepresentationTheory.Dual
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.Quotient
import TauCeti.RepresentationTheory.Stabilizer

/-!
# Ramification of global Galois representations

Let `F` be a field (a number field in the case of interest), `G_F` its absolute Galois group and
`O` the integral closure of `𝓞 F` in `F^alg`. For a finite place `v` of `F`, a height-one prime of
`𝓞 F`, a continuous representation `ρ` of `G_F` is **unramified at `v`** if the inertia group `I_Q`
(`TauCeti.GaloisRep.inertiaGroup`) acts trivially for every maximal ideal `Q` of `O` above `v`.
The **ramification set** of `ρ` is the set of finite places at which `ρ` is ramified.

The ramification set of a product is the union of the ramification sets, and those of a tensor
product, of a contragredient, of an equivariant quotient and of a scalar extension (in particular
of a raw reduction) are contained in the expected sets. The trivial representation is unramified
everywhere, and isomorphic representations have the same ramification set.

The definition quantifies over all maximal ideals above `v`. Over a perfect field `G_F` permutes
them transitively and `I_{σQ} = σ I_Q σ⁻¹`, so one of them suffices
(`isUnramifiedAt_iff_of_isMaximal`, `isUnramifiedAt_iff_exists`). A representation is
**unramified outside** a set `S` of finite places if its ramification set is contained in `S`. The
finiteness of the ramification set for a representation with open kernel is not proved here.

## Main definitions

* `TauCeti.ContinuousRep.IsUnramifiedAt ρ v`: `ρ(I_Q) = 1` for every maximal `Q` of `O` above `v`.
* `TauCeti.ContinuousRep.ramificationSet ρ`: the finite places at which `ρ` is ramified.
* `TauCeti.ContinuousRep.IsUnramifiedOutside ρ S`: `ρ` is unramified at every finite place outside
  `S`.

## Main results

* `TauCeti.ContinuousRep.isUnramifiedAt_iff_of_isMaximal`, `isUnramifiedAt_iff_exists`: over a
  perfect field, respectively a number field, one maximal ideal above `v` suffices.
* `TauCeti.ContinuousRep.ramificationSet_trivial`: the trivial representation is unramified
  everywhere.
* `TauCeti.ContinuousRep.ramificationSet_prod`: `Ram(ρ × ρ') = Ram ρ ∪ Ram ρ'`.
* `TauCeti.ContinuousRep.ramificationSet_tprod_subset`: `Ram(ρ ⊗ ρ') ⊆ Ram ρ ∪ Ram ρ'`.
* `TauCeti.ContinuousRep.ramificationSet_dual_subset`: `Ram(ρ^∨) ⊆ Ram ρ`.
* `TauCeti.ContinuousRep.ramificationSet_subset_of_surjective`: an equivariant quotient is
  unramified wherever the representation is.
* `TauCeti.ContinuousRep.ramificationSet_baseChange_subset`: `Ram(B ⊗ ρ) ⊆ Ram ρ`.

Each bound comes with its form at a single place: `isUnramifiedAt_trivial`,
`isUnramifiedAt_prod_iff`, `IsUnramifiedAt.tprod`, `IsUnramifiedAt.dual`,
`IsUnramifiedAt.of_surjective`, `IsUnramifiedAt.baseChange` and `Iso.isUnramifiedAt_iff`.

-/

public section

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace TauCeti.ContinuousRep

variable {F : Type*} [Field F]

section Predicates

variable {A M N : Type*} [Semiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [AddCommMonoid N] [Module A N] [TopologicalSpace N]

/-- A continuous representation of `G_F` is **unramified at the finite place `v`** if the inertia
group `I_Q` acts trivially for every maximal ideal `Q` of the integral closure of `𝓞 F` in `F^alg`
lying over `v`. -/
def IsUnramifiedAt (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M)
    (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)), Q.IsMaximal →
    Q.under (𝓞 F) = v.asIdeal → GaloisRep.inertiaGroup F Q ≤ ρ.toRepresentation.ker

/-- The **ramification set** of a continuous representation of `G_F`: the finite places at which
it is ramified. -/
def ramificationSet (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) :
    Set (HeightOneSpectrum (𝓞 F)) :=
  {v | ¬ρ.IsUnramifiedAt v}

variable {ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M}
  {ρ' : ContinuousRep (Field.absoluteGaloisGroup F) A N} {v : HeightOneSpectrum (𝓞 F)}

theorem isUnramifiedAt_iff :
    ρ.IsUnramifiedAt v ↔ ∀ Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)),
      Q.IsMaximal → Q.under (𝓞 F) = v.asIdeal → ∀ σ ∈ GaloisRep.inertiaGroup F Q, ρ σ = 1 :=
  Iff.rfl

@[simp]
theorem mem_ramificationSet_iff : v ∈ ρ.ramificationSet ↔ ¬ρ.IsUnramifiedAt v :=
  Iff.rfl

/-- A representation is unramified at `v` exactly when `v` is outside its ramification set. -/
theorem notMem_ramificationSet_iff : v ∉ ρ.ramificationSet ↔ ρ.IsUnramifiedAt v :=
  not_not

/-- If every element acting trivially in `ρ` acts trivially in `τ`, possibly over other
coefficients, then `τ` is unramified wherever `ρ` is. -/
theorem IsUnramifiedAt.of_ker_le {B P : Type*} [Semiring B] [AddCommMonoid P] [Module B P]
    [TopologicalSpace P] {τ : ContinuousRep (Field.absoluteGaloisGroup F) B P}
    (h : ρ.IsUnramifiedAt v) (hker : ρ.toRepresentation.ker ≤ τ.toRepresentation.ker) :
    τ.IsUnramifiedAt v :=
  fun Q hQ hv ↦ (h Q hQ hv).trans hker

/-- If every element acting trivially in `ρ` acts trivially in `τ`, possibly over other
coefficients, then `Ram τ ⊆ Ram ρ`. -/
theorem ramificationSet_subset_of_ker_le {B P : Type*} [Semiring B] [AddCommMonoid P]
    [Module B P] [TopologicalSpace P] {τ : ContinuousRep (Field.absoluteGaloisGroup F) B P}
    (hker : ρ.toRepresentation.ker ≤ τ.toRepresentation.ker) :
    τ.ramificationSet ⊆ ρ.ramificationSet :=
  fun _ hv h ↦ hv (h.of_ker_le hker)

variable (F A M) in
/-- The trivial representation is unramified at every finite place. -/
@[simp]
theorem isUnramifiedAt_trivial (v : HeightOneSpectrum (𝓞 F)) :
    (trivial (Field.absoluteGaloisGroup F) A M).IsUnramifiedAt v := fun _ _ _ ↦ by
  rw [toRepresentation_trivial, Representation.ker_trivial]
  exact le_top

variable (F A M) in
/-- The trivial representation is unramified everywhere. -/
@[simp]
theorem ramificationSet_trivial : (trivial (Field.absoluteGaloisGroup F) A M).ramificationSet = ∅ :=
  Set.eq_empty_of_forall_notMem fun v hv ↦ hv (isUnramifiedAt_trivial F A M v)

/-- A product is unramified at `v` exactly when both factors are. -/
@[simp]
theorem isUnramifiedAt_prod_iff :
    (ρ.prod ρ').IsUnramifiedAt v ↔ ρ.IsUnramifiedAt v ∧ ρ'.IsUnramifiedAt v := by
  simp only [IsUnramifiedAt, toRepresentation_prod, Representation.ker_prod, le_inf_iff]
  exact ⟨fun h ↦ ⟨fun Q hQ hv ↦ (h Q hQ hv).1, fun Q hQ hv ↦ (h Q hQ hv).2⟩,
    fun h Q hQ hv ↦ ⟨h.1 Q hQ hv, h.2 Q hQ hv⟩⟩

/-- **The ramification set of a product** is the union of the ramification sets. -/
@[simp]
theorem ramificationSet_prod :
    (ρ.prod ρ').ramificationSet = ρ.ramificationSet ∪ ρ'.ramificationSet := by
  ext v
  simp only [mem_ramificationSet_iff, Set.mem_union, isUnramifiedAt_prod_iff, not_and_or]

/-- Isomorphic representations are unramified at the same finite places. -/
theorem Iso.isUnramifiedAt_iff (e : Iso ρ ρ') : ρ.IsUnramifiedAt v ↔ ρ'.IsUnramifiedAt v :=
  ⟨fun h ↦ h.of_ker_le e.toRepresentationEquiv.ker_eq.le,
    fun h ↦ h.of_ker_le e.toRepresentationEquiv.ker_eq.ge⟩

/-- Isomorphic representations have the same ramification set. -/
theorem Iso.ramificationSet_eq (e : Iso ρ ρ') : ρ.ramificationSet = ρ'.ramificationSet :=
  Set.ext fun _ ↦ e.isUnramifiedAt_iff.not

/-- An equivariant quotient of a representation unramified at `v` is unramified at `v`. -/
theorem IsUnramifiedAt.of_surjective (h : ρ.IsUnramifiedAt v) (f : Hom ρ ρ')
    (hf : Function.Surjective f) : ρ'.IsUnramifiedAt v :=
  h.of_ker_le (f.toIntertwiningMap.ker_le_ker_of_surjective hf)

/-- An equivariant quotient is unramified wherever the representation is. -/
theorem ramificationSet_subset_of_surjective (f : Hom ρ ρ') (hf : Function.Surjective f) :
    ρ'.ramificationSet ⊆ ρ.ramificationSet :=
  fun _ hv h ↦ hv (h.of_surjective f hf)

/-! ### One prime above `v` suffices -/

/-- Over a perfect field (for instance a number field), unramifiedness at `v` can be tested at a
single maximal ideal `Q` of the integral closure of `𝓞 F` in `F^alg` above `v`. -/
theorem isUnramifiedAt_iff_of_isMaximal [PerfectField F]
    {Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))} (hQ : Q.IsMaximal)
    (hQv : Q.under (𝓞 F) = v.asIdeal) :
    ρ.IsUnramifiedAt v ↔ GaloisRep.inertiaGroup F Q ≤ ρ.toRepresentation.ker := by
  -- The primes above `v` are `G_F`-conjugate, so are their inertia groups, and `ker ρ` is normal.
  refine ⟨fun h ↦ h Q hQ hQv, fun h Q' hQ' hQ'v ↦ ?_⟩
  have := hQ.isPrime
  have := hQ'.isPrime
  obtain ⟨σ, hσ⟩ := GaloisRep.exists_inertiaGroup_eq_map_conj Q Q' (hQv.trans hQ'v.symm)
  rw [hσ, Subgroup.map_le_iff_le_comap]
  intro g hg
  rw [Subgroup.mem_comap, MonoidHom.coe_ofClass, MulAut.conj_apply]
  exact (MonoidHom.normal_ker ρ.toRepresentation).conj_mem g (h hg) σ

/-- **`isUnramifiedAt_iff_exists`**: over a number field, `ρ` is unramified at `v` exactly when the
inertia group at some maximal ideal of the integral closure of `𝓞 F` in `F^alg` above `v` acts
trivially. -/
theorem isUnramifiedAt_iff_exists [NumberField F] :
    ρ.IsUnramifiedAt v ↔ ∃ Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)),
      Q.IsMaximal ∧ Q.under (𝓞 F) = v.asIdeal ∧
        GaloisRep.inertiaGroup F Q ≤ ρ.toRepresentation.ker := by
  refine ⟨fun h ↦ ?_, fun ⟨Q, hQ, hQv, h⟩ ↦ (isUnramifiedAt_iff_of_isMaximal hQ hQv).2 h⟩
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := integralClosure (𝓞 F) (AlgebraicClosure F)) v.asIdeal
  have hQv : Q.under (𝓞 F) = v.asIdeal := ((Ideal.liesOver_iff _ _).1 hQv).symm
  exact ⟨Q, hQ, hQv, h Q hQ hQv⟩

/-! ### Unramified outside a set of places -/

/-- A continuous representation of `G_F` is **unramified outside** a set `S` of finite places if
it is unramified at every finite place not in `S`, that is, if its ramification set is contained
in `S`. Typically `S` is finite. -/
def IsUnramifiedOutside (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M)
    (S : Set (HeightOneSpectrum (𝓞 F))) : Prop :=
  ρ.ramificationSet ⊆ S

/-- `ρ` is unramified outside `S` exactly when its ramification set is contained in `S`. -/
theorem isUnramifiedOutside_iff_ramificationSet_subset {S : Set (HeightOneSpectrum (𝓞 F))} :
    ρ.IsUnramifiedOutside S ↔ ρ.ramificationSet ⊆ S :=
  Iff.rfl

/-- `ρ` is unramified outside `S` exactly when it is unramified at every finite place not in `S`. -/
theorem isUnramifiedOutside_iff {S : Set (HeightOneSpectrum (𝓞 F))} :
    ρ.IsUnramifiedOutside S ↔ ∀ v ∉ S, ρ.IsUnramifiedAt v := by
  rw [isUnramifiedOutside_iff_ramificationSet_subset]
  refine forall_congr' fun v ↦ ?_
  rw [mem_ramificationSet_iff, not_imp_comm]

/-- A representation is unramified outside its own ramification set. -/
theorem isUnramifiedOutside_ramificationSet : ρ.IsUnramifiedOutside ρ.ramificationSet :=
  isUnramifiedOutside_iff_ramificationSet_subset.2 subset_rfl

/-- Being unramified outside `S` is inherited by larger sets of places. -/
theorem IsUnramifiedOutside.mono {S T : Set (HeightOneSpectrum (𝓞 F))}
    (h : ρ.IsUnramifiedOutside S) (hST : S ⊆ T) : ρ.IsUnramifiedOutside T := by
  rw [isUnramifiedOutside_iff_ramificationSet_subset] at h ⊢
  exact h.trans hST

/-- If every element acting trivially in `ρ` acts trivially in `τ`, then `τ` is unramified
outside every set outside which `ρ` is. -/
theorem IsUnramifiedOutside.of_ker_le {B P : Type*} [Semiring B] [AddCommMonoid P] [Module B P]
    [TopologicalSpace P] {τ : ContinuousRep (Field.absoluteGaloisGroup F) B P}
    {S : Set (HeightOneSpectrum (𝓞 F))} (h : ρ.IsUnramifiedOutside S)
    (hker : ρ.toRepresentation.ker ≤ τ.toRepresentation.ker) : τ.IsUnramifiedOutside S := by
  rw [isUnramifiedOutside_iff_ramificationSet_subset] at h ⊢
  exact (ramificationSet_subset_of_ker_le hker).trans h

/-- A product is unramified outside `S` exactly when both factors are. -/
@[simp]
theorem isUnramifiedOutside_prod_iff {S : Set (HeightOneSpectrum (𝓞 F))} :
    (ρ.prod ρ').IsUnramifiedOutside S ↔ ρ.IsUnramifiedOutside S ∧ ρ'.IsUnramifiedOutside S := by
  simp only [isUnramifiedOutside_iff_ramificationSet_subset, ramificationSet_prod,
    Set.union_subset_iff]

/-- Isomorphic representations are unramified outside the same sets of places. -/
theorem Iso.isUnramifiedOutside_iff (e : Iso ρ ρ') {S : Set (HeightOneSpectrum (𝓞 F))} :
    ρ.IsUnramifiedOutside S ↔ ρ'.IsUnramifiedOutside S := by
  simp only [isUnramifiedOutside_iff_ramificationSet_subset, e.ramificationSet_eq]

/-- The trivial representation is unramified outside every set of places. -/
@[simp]
theorem isUnramifiedOutside_trivial (S : Set (HeightOneSpectrum (𝓞 F))) :
    (trivial (Field.absoluteGaloisGroup F) A M).IsUnramifiedOutside S := by
  simp [isUnramifiedOutside_iff_ramificationSet_subset]

/-- An equivariant quotient of a representation unramified outside `S` is unramified outside `S`. -/
theorem IsUnramifiedOutside.of_surjective {S : Set (HeightOneSpectrum (𝓞 F))}
    (h : ρ.IsUnramifiedOutside S) (f : Hom ρ ρ') (hf : Function.Surjective f) :
    ρ'.IsUnramifiedOutside S := by
  rw [isUnramifiedOutside_iff_ramificationSet_subset] at h ⊢
  exact (ramificationSet_subset_of_surjective f hf).trans h

end Predicates

section Tensor

variable {A M N : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [AddCommGroup M]
  [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M] [AddCommGroup N]
  [Module A N] [TopologicalSpace N] [IsModuleTopology A N] [Module.Finite A N]
  [TopologicalSpace (M ⊗[A] N)] [IsModuleTopology A (M ⊗[A] N)]

/-- A tensor product of representations unramified at `v` is unramified at `v`. -/
theorem IsUnramifiedAt.tprod {ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M}
    {ρ' : ContinuousRep (Field.absoluteGaloisGroup F) A N} {v : HeightOneSpectrum (𝓞 F)}
    (h : ρ.IsUnramifiedAt v) (h' : ρ'.IsUnramifiedAt v) : (ρ.tprod ρ').IsUnramifiedAt v :=
  fun Q hQ hQv ↦ by
    rw [toRepresentation_tprod]
    exact (le_inf (h Q hQ hQv) (h' Q hQ hQv)).trans (Representation.ker_inf_ker_le_ker_tprod _ _)

/-- **The ramification set of a tensor product** is contained in the union of the ramification
sets. -/
theorem ramificationSet_tprod_subset (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M)
    (ρ' : ContinuousRep (Field.absoluteGaloisGroup F) A N) :
    (ρ.tprod ρ').ramificationSet ⊆ ρ.ramificationSet ∪ ρ'.ramificationSet := by
  intro v hv
  rw [Set.mem_union, mem_ramificationSet_iff, mem_ramificationSet_iff, ← not_and_or]
  exact fun h ↦ hv (h.1.tprod h.2)

/-- A tensor product of representations unramified outside `S` is unramified outside `S`. -/
theorem IsUnramifiedOutside.tprod {ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M}
    {ρ' : ContinuousRep (Field.absoluteGaloisGroup F) A N} {S : Set (HeightOneSpectrum (𝓞 F))}
    (h : ρ.IsUnramifiedOutside S) (h' : ρ'.IsUnramifiedOutside S) :
    (ρ.tprod ρ').IsUnramifiedOutside S := by
  rw [isUnramifiedOutside_iff_ramificationSet_subset] at h h' ⊢
  exact (ramificationSet_tprod_subset ρ ρ').trans (Set.union_subset h h')

end Tensor

section Dual

variable {A M : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [AddCommGroup M]
  [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]
  [Module.Projective A M] [TopologicalSpace (Module.Dual A M)]
  [IsModuleTopology A (Module.Dual A M)]

/-- The contragredient of a representation unramified at `v` is unramified at `v`. -/
theorem IsUnramifiedAt.dual {ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M}
    {v : HeightOneSpectrum (𝓞 F)} (h : ρ.IsUnramifiedAt v) : ρ.dual.IsUnramifiedAt v :=
  h.of_ker_le (by
    rw [toRepresentation_dual]
    exact ρ.toRepresentation.ker_le_ker_dual)

/-- **The ramification set of the contragredient** is contained in that of the representation. -/
theorem ramificationSet_dual_subset (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) :
    ρ.dual.ramificationSet ⊆ ρ.ramificationSet :=
  fun _ hv h ↦ hv h.dual

/-- The contragredient of a representation unramified outside `S` is unramified outside `S`. -/
theorem IsUnramifiedOutside.dual {ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M}
    {S : Set (HeightOneSpectrum (𝓞 F))} (h : ρ.IsUnramifiedOutside S) :
    ρ.dual.IsUnramifiedOutside S := by
  rw [isUnramifiedOutside_iff_ramificationSet_subset] at h ⊢
  exact (ramificationSet_dual_subset ρ).trans h

end Dual

section BaseChange

variable {A M : Type*} [CommSemiring A] [TopologicalSpace A] [AddCommMonoid M] [Module A M]
  [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M] (B : Type*) [Ring B]
  [TopologicalSpace B] [IsTopologicalSemiring B] [Algebra A B] [ContinuousSMul A B]
  [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]

/-- The scalar extension `B ⊗ ρ` of a representation unramified at `v` is unramified at `v`. -/
theorem IsUnramifiedAt.baseChange {ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M}
    {v : HeightOneSpectrum (𝓞 F)} (h : ρ.IsUnramifiedAt v) : (ρ.baseChange B).IsUnramifiedAt v :=
  h.of_ker_le (by
    rw [toRepresentation_baseChange]
    exact ρ.toRepresentation.ker_le_ker_baseChange B)

/-- **Extension of scalars does not create ramification**: `Ram(B ⊗ ρ) ⊆ Ram ρ`. For `B` the
residue field this says that a raw reduction is unramified wherever the representation is; the
converse fails. -/
theorem ramificationSet_baseChange_subset (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) :
    (ρ.baseChange B).ramificationSet ⊆ ρ.ramificationSet :=
  fun _ hv h ↦ hv (h.baseChange B)

/-- The scalar extension `B ⊗ ρ` of a representation unramified outside `S` is unramified
outside `S`. -/
theorem IsUnramifiedOutside.baseChange {ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M}
    {S : Set (HeightOneSpectrum (𝓞 F))} (h : ρ.IsUnramifiedOutside S) :
    (ρ.baseChange B).IsUnramifiedOutside S := by
  rw [isUnramifiedOutside_iff_ramificationSet_subset] at h ⊢
  exact (ramificationSet_baseChange_subset B ρ).trans h

end BaseChange

end TauCeti.ContinuousRep
