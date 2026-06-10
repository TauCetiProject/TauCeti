/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.Coalgebra.Comodule

/-!
# Subcomodules

This file defines subcomodules of a right comodule over a coalgebra: submodules whose
coaction factors through the tensor product of the submodule with the coalgebra.

The reductive-groups roadmap asks for finite-dimensional subcomodules and the fundamental
theorem of comodules. This file supplies the first small piece of that infrastructure:
the stability predicate and the bundled subtype of stable submodules.

## Main definitions

* `TauCeti.IsSubcomodule`: the predicate that a submodule is stable under the coaction.
* `TauCeti.Subcomodule`: a submodule satisfying `IsSubcomodule`.

## References

This is standard coalgebra language, added for
`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1 target "Finite-dimensional
subcoalgebras (the fundamental theorem of comodules)" and its statement that every comodule
is the union of its finite-dimensional subcomodules.
-/

open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The image of `P ⊗ C` in `M ⊗ C` induced by the inclusion of a submodule `P ≤ M`. -/
def submoduleCoactionRange (P : Submodule R M) : Submodule R (M ⊗[R] C) :=
  LinearMap.range (P.subtype.rTensor C)

omit [Coalgebra R C] [Comodule R C M] in
/-- Membership in the coaction range means being the image of some tensor in `P ⊗ C`. -/
@[simp]
theorem mem_submoduleCoactionRange (P : Submodule R M) (x : M ⊗[R] C) :
    x ∈ submoduleCoactionRange (R := R) (C := C) P ↔
      ∃ y : P ⊗[R] C,
        P.subtype.rTensor C y = x :=
  LinearMap.mem_range

/-- A submodule of a right comodule is a subcomodule if the image of its coaction lies in the
range of `P ⊗ C → M ⊗ C`. -/
def IsSubcomodule (P : Submodule R M) : Prop :=
  P.map (Comodule.coact (R := R) (C := C) (M := M)) ≤
    LinearMap.range (P.subtype.rTensor C)

/-- Definitional restatement of `IsSubcomodule` using the named coaction range. -/
theorem isSubcomodule_def (P : Submodule R M) :
    IsSubcomodule (R := R) (C := C) (M := M) P ↔
      P.map (Comodule.coact (R := R) (C := C) (M := M)) ≤
        submoduleCoactionRange (R := R) (C := C) P :=
  Iff.rfl

/-- A subcomodule of a right comodule, bundled as a coaction-stable submodule. -/
structure Subcomodule (R : Type u) (C : Type v) (M : Type w) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M]
    [Comodule R C M] where
  /-- The underlying submodule. -/
  toSubmodule : Submodule R M
  /-- The underlying submodule is stable under the coaction. -/
  isSubcomodule : IsSubcomodule (R := R) (C := C) (M := M) toSubmodule

/-- The elementwise characterization of `IsSubcomodule`: the coaction of every element of `P`
is represented by an element of `P ⊗ C`. -/
theorem isSubcomodule_iff (P : Submodule R M) :
    IsSubcomodule (R := R) (C := C) (M := M) P ↔
      ∀ ⦃m : M⦄, m ∈ P →
        ∃ y : P ⊗[R] C,
          P.subtype.rTensor C y = Comodule.coact (R := R) (C := C) (M := M) m := by
  constructor
  · intro hP m hm
    exact (mem_submoduleCoactionRange (R := R) (C := C) P _).mp (hP ⟨m, hm, rfl⟩)
  · intro hP x hx
    rcases hx with ⟨m, hm, rfl⟩
    exact (mem_submoduleCoactionRange (R := R) (C := C) P _).mpr (hP hm)

namespace Subcomodule

@[ext]
theorem ext {P Q : Subcomodule R C M} (h : P.toSubmodule = Q.toSubmodule) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

@[simp]
theorem toSubmodule_mk (P : Submodule R M)
    (hP : IsSubcomodule (R := R) (C := C) (M := M) P) :
    toSubmodule (mk (R := R) (C := C) (M := M) P hP) = P :=
  rfl

/-- The coaction of an element of a subcomodule factors through `P ⊗ C`. -/
theorem coact_mem (P : Subcomodule R C M) ⦃m : M⦄ (hm : m ∈ P.toSubmodule) :
    Comodule.coact (R := R) (C := C) (M := M) m ∈
      submoduleCoactionRange (R := R) (C := C) P.toSubmodule :=
  P.isSubcomodule ⟨m, hm, rfl⟩

end Subcomodule

end TauCeti
