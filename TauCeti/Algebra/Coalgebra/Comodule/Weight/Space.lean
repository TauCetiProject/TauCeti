/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Vector
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Weight spaces of a comodule

Let `M` be a comodule over a coalgebra `C` over a commutative semiring. For a group-like element
`c` of `C`, its weight space is the submodule of vectors whose coaction is `m ↦ m ⊗ c`. This
file packages that submodule and its elementary functorial API. Over a domain, when `C` is
projective and `M` is torsion-free, it proves that the weight spaces belonging to distinct
group-like elements are independent. Consequently a Noetherian comodule has only finitely many
nonzero weight spaces.

The independence proof reads a coaction through all linear functionals on `C`. The `c`-weight
space is the joint eigenspace of the component endomorphisms
`Comodule.coactComponent φ`, with eigenvalue function `φ ↦ φ c`. Linear functionals separate
points when `C` is projective, so distinct group-like elements give distinct joint eigenvalue
functions.

Unlike the weight decomposition for a monoid algebra, these weight spaces need not span an
arbitrary comodule. Their finite nonzero support can be used to define permutation actions on
weights in Lie--Kolchin arguments.

## Main declarations

* `TauCeti.GroupLike.weightSpace`: the weight space belonging to a group-like element.
* `TauCeti.GroupLike.weightSubcomodule`: the weight space as a subcomodule.
* `TauCeti.Comodule.iSupIndep_groupLikeWeightSpace`: distinct group-like weight spaces are
  independent.
* `TauCeti.Comodule.finite_setOf_groupLikeWeightSpace_ne_bot`: a Noetherian comodule has only
  finitely many nonzero group-like weight spaces.
* `TauCeti.Comodule.NonzeroGroupLikeWeight`: the group-like elements with nonzero weight space.
* `TauCeti.Comodule.natCard_nonzeroGroupLikeWeights_le_finrank`: the number of nonzero weight
  spaces is at most the dimension of the comodule.
* `TauCeti.Comodule.hasNonzeroWeightVector_iff_exists_groupLikeWeightSpace_ne_bot`: nonzero weight
  vectors are exactly nontrivial group-like weight spaces.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Theorem 6.3.1.
-/

public section

open scoped TensorProduct

universe u v w x

noncomputable section

section Semiring

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [TauCeti.Comodule R C M]
variable [AddCommMonoid N] [Module R N] [TauCeti.Comodule R C N]

namespace TauCeti.GroupLike

/-- The weight space of a group-like element `c` consists of the vectors with coaction
`m ↦ m ⊗ c`. -/
def weightSpace (c : GroupLike R C) : Submodule R M :=
  LinearMap.eqLocus (TauCeti.Comodule.coact (R := R) (C := C) (M := M))
    ((TensorProduct.mk R M C).flip c.val)

/-- Membership in a group-like weight space is the corresponding coaction equation. -/
@[simp]
theorem mem_weightSpace {c : GroupLike R C} {m : M} :
    m ∈ weightSpace (M := M) c ↔
      TauCeti.Comodule.coact (R := R) (C := C) m = m ⊗ₜ[R] c.val :=
  LinearMap.mem_eqLocus

/-- A group-like weight space, regarded as a subcomodule. -/
def weightSubcomodule (c : GroupLike R C) : TauCeti.Subcomodule R C M :=
  TauCeti.Subcomodule.ofSubmodule (weightSpace (M := M) c) fun m hm => by
    refine ⟨⟨m, hm⟩ ⊗ₜ[R] c.val, ?_⟩
    rw [TensorProduct.map_tmul]
    simpa using (mem_weightSpace.mp hm).symm

/-- The underlying submodule of the group-like weight subcomodule is its weight space. -/
@[simp]
theorem weightSubcomodule_toSubmodule (c : GroupLike R C) :
    (weightSubcomodule (M := M) c).toSubmodule = weightSpace (M := M) c :=
  TauCeti.Subcomodule.ofSubmodule_carrier _ _

/-- Membership in the group-like weight subcomodule is the corresponding coaction equation. -/
@[simp]
theorem mem_weightSubcomodule {c : GroupLike R C} {m : M} :
    m ∈ weightSubcomodule (M := M) c ↔
      TauCeti.Comodule.coact (R := R) (C := C) m = m ⊗ₜ[R] c.val :=
  mem_weightSpace

end TauCeti.GroupLike

namespace TauCeti.Comodule

/-- The group-like elements whose weight space in a comodule is nonzero. -/
abbrev NonzeroGroupLikeWeight (R : Type u) (C : Type v) (M : Type w)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M] :=
  {c : GroupLike R C // TauCeti.GroupLike.weightSpace (M := M) c ≠ ⊥}

/-- A comodule morphism preserves every group-like weight space. -/
theorem Hom.map_mem_groupLikeWeightSpace (f : Hom R C M N) {c : GroupLike R C} {m : M}
    (hm : m ∈ TauCeti.GroupLike.weightSpace (M := M) c) :
    f m ∈ TauCeti.GroupLike.weightSpace (M := N) c := by
  rw [TauCeti.GroupLike.mem_weightSpace] at hm ⊢
  rw [← f.map_coact_apply, hm, TensorProduct.map_tmul]
  rfl

/-- A comodule morphism maps each group-like weight space into the same weight space. -/
theorem Hom.map_groupLikeWeightSpace_le (f : Hom R C M N) (c : GroupLike R C) :
    (TauCeti.GroupLike.weightSpace (M := M) c).map f.toLinearMap ≤
      TauCeti.GroupLike.weightSpace (M := N) c := by
  rintro _ ⟨m, hm, rfl⟩
  exact f.map_mem_groupLikeWeightSpace hm

/-- A comodule has a nonzero weight vector exactly when one of its group-like weight spaces is
nonzero. -/
theorem hasNonzeroWeightVector_iff_exists_groupLikeWeightSpace_ne_bot :
    HasNonzeroWeightVector R C M ↔
      ∃ c : GroupLike R C, TauCeti.GroupLike.weightSpace (M := M) c ≠ ⊥ := by
  rw [hasNonzeroWeightVector_iff]
  constructor
  · rintro ⟨m, c, hm, hc, hcoact⟩
    refine ⟨⟨c, hc⟩, ?_⟩
    exact (TauCeti.GroupLike.weightSpace (M := M) ⟨c, hc⟩).ne_bot_iff.mpr
      ⟨m, TauCeti.GroupLike.mem_weightSpace.mpr hcoact, hm⟩
  · rintro ⟨c, hc⟩
    obtain ⟨m, hm, hm0⟩ :=
      (TauCeti.GroupLike.weightSpace (M := M) c).ne_bot_iff.mp hc
    exact ⟨m, c.val, hm0, c.isGroupLikeElem_val, TauCeti.GroupLike.mem_weightSpace.mp hm⟩

end TauCeti.Comodule

end Semiring

namespace TauCeti

namespace Comodule

section Projective

variable {k : Type u} {C : Type v} {M : Type w}
variable [CommSemiring k] [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [Module.Projective k C]
variable [AddCommMonoid M] [Module k M] [Comodule k C M]

/-- A vector has weight `c` exactly when every component of its coaction has eigenvalue obtained
by evaluating the component functional at `c`. -/
theorem mem_groupLikeWeightSpace_iff_forall_coactComponent_eq_smul
    {c : GroupLike k C} {m : M} :
    m ∈ TauCeti.GroupLike.weightSpace (M := M) c ↔
      ∀ φ : Module.Dual k C,
        coactComponent (R := k) (C := C) (M := M) φ m = φ c.val • m := by
  constructor
  · intro hm φ
    rw [coactComponent_apply, TauCeti.GroupLike.mem_weightSpace.mp hm,
      TauCeti.LinearMap.tensorComponent_tmul]
  · intro hm
    rw [TauCeti.GroupLike.mem_weightSpace]
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro φ
    rw [← coactComponent_apply, hm φ, TauCeti.LinearMap.tensorComponent_tmul]

end Projective

end Comodule

namespace GroupLike

section RingProjective

variable {k : Type u} {C : Type v} {M : Type w}
variable [CommRing k] [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [Module.Projective k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]

/-- A group-like weight space is the joint eigenspace of all components of the coaction. -/
theorem weightSpace_eq_iInf_eigenspace (c : GroupLike k C) :
    weightSpace (M := M) c =
      ⨅ φ : Module.Dual k C,
        Module.End.eigenspace (Comodule.coactComponent (R := k) (C := C) (M := M) φ)
          (φ c.val) := by
  ext m
  rw [Comodule.mem_groupLikeWeightSpace_iff_forall_coactComponent_eq_smul]
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

end RingProjective


end GroupLike

namespace Comodule

section Domain

variable {k : Type u} {C : Type v} {M : Type w}
variable [CommRing k] [IsDomain k] [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [Module.Projective k C] [AddCommGroup M] [Module k M] [Module.IsTorsionFree k M]
variable [Comodule k C M]

/-- The group-like weight spaces of a torsion-free comodule over a domain are
supremum-independent. -/
theorem iSupIndep_groupLikeWeightSpace :
    iSupIndep (GroupLike.weightSpace (M := M) : GroupLike k C → Submodule k M) := by
  have h := iSupIndep_iInf_eigenspace
    (fun φ : Module.Dual k C ↦
      (coactComponent (R := k) (C := C) (M := M) φ : Module.End k M))
  have hEval :
      Function.Injective (fun c : GroupLike k C ↦ fun φ : Module.Dual k C ↦ φ c.val) := by
    intro c d hcd
    apply GroupLike.val_injective
    apply Module.eval_apply_injective k
    ext φ
    exact congrFun hcd φ
  have hc := h.comp hEval
  have hfamily :
      ((fun χ : Module.Dual k C → k ↦
        ⨅ φ : Module.Dual k C,
          Module.End.eigenspace (coactComponent (R := k) (C := C) (M := M) φ) (χ φ)) ∘
          fun c : GroupLike k C ↦ fun φ : Module.Dual k C ↦ φ c.val) =
        (GroupLike.weightSpace (M := M) : GroupLike k C → Submodule k M) := by
    funext c
    exact (GroupLike.weightSpace_eq_iInf_eigenspace c).symm
  rw [hfamily] at hc
  exact hc

/-- A Noetherian comodule has only finitely many nonzero group-like weight spaces. -/
theorem finite_setOf_groupLikeWeightSpace_ne_bot [IsNoetherian k M] :
    {c : GroupLike k C | GroupLike.weightSpace (M := M) c ≠ ⊥}.Finite :=
  Submodule.finite_ne_bot_of_iSupIndep iSupIndep_groupLikeWeightSpace

/-- The nonzero group-like weights of a Noetherian comodule form a finite type. -/
noncomputable instance instFiniteNonzeroGroupLikeWeight [IsNoetherian k M] :
    Finite (NonzeroGroupLikeWeight k C M) :=
  finite_setOf_groupLikeWeightSpace_ne_bot.to_subtype

end Domain

section Field

variable {k : Type u} {C : Type v} {M : Type w}
variable [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]

/-- The number of nonzero group-like weight spaces of a finite-dimensional comodule is at most
the dimension of the comodule. -/
theorem natCard_nonzeroGroupLikeWeights_le_finrank [FiniteDimensional k M] :
    Nat.card (NonzeroGroupLikeWeight k C M) ≤ Module.finrank k M := by
  let _ : Fintype (NonzeroGroupLikeWeight k C M) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact iSupIndep.subtype_ne_bot_le_finrank (R := k) (M := M)
    iSupIndep_groupLikeWeightSpace

end Field

end Comodule

end TauCeti

end
