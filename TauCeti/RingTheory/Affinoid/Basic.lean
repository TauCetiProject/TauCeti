/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Affinoid algebras

An affinoid algebra is a quotient of a Tate algebra in finitely many variables. The predicate
`TauCeti.IsAffinoidAlgebra` is algebraic: it chooses neither a norm nor a topology. In particular,
it includes nonreduced algebras and the zero algebra. The native restricted-series subring at
unit polyradius is used throughout.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries

variable (K : Type*) [NormedField K] [IsUltrametricDist K] (A : Type*) [CommRing A] [Algebra K A]

/-- An affinoid algebra is a quotient of a finite-variable Tate algebra, without a choice of
norm or topology on the quotient. -/
def IsAffinoidAlgebra : Prop :=
  ∃ (n : ℕ) (π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A),
    Function.Surjective π

/-- The presentation criterion for an affinoid algebra. -/
theorem isAffinoidAlgebra_iff : IsAffinoidAlgebra K A ↔
    ∃ (n : ℕ) (π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A),
      Function.Surjective π := Iff.rfl

variable {K A}

/-- A Tate algebra in finitely many variables is affinoid. -/
theorem isAffinoidAlgebra_tate {σ : Type*} [Finite σ] :
    IsAffinoidAlgebra K (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) := by
  let := Fintype.ofFinite σ
  let e : IsRestricted.subring (R := K) (fun _ : Fin (Fintype.card σ) ↦ 1) ≃ₐ[K]
      IsRestricted.subring (R := K) (fun _ : σ ↦ 1) :=
    IsRestricted.renameAlgEquiv (Fintype.equivFin σ).symm fun _ ↦ 1
  exact (isAffinoidAlgebra_iff K _).mpr ⟨_, e.toAlgHom, e.surjective⟩

/-- The coefficient field is affinoid, using the Tate presentation in zero variables. -/
theorem isAffinoidAlgebra_self : IsAffinoidAlgebra K K := by
  let f : IsRestricted.subring (R := K) (fun _ : Fin 0 ↦ 1) →ₐ[K] K :=
    { toRingHom := constantCoeff.comp (IsRestricted.subring (R := K) (fun _ : Fin 0 ↦ 1)).subtype
      commutes' r := by simp [coe_algebraMap_isRestrictedSubring] }
  exact (isAffinoidAlgebra_iff K K).mpr ⟨0, f, fun r ↦ ⟨algebraMap K _ r, f.commutes r⟩⟩

namespace IsAffinoidAlgebra

/-- A surjective image of an affinoid algebra is affinoid. -/
theorem of_surjective (hA : IsAffinoidAlgebra K A) {B : Type*} [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (hf : Function.Surjective f) : IsAffinoidAlgebra K B := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  exact (isAffinoidAlgebra_iff K B).mpr ⟨n, f.comp π, hf.comp hπ⟩

/-- Every quotient of an affinoid algebra is affinoid, including the zero quotient. -/
theorem quotient (hA : IsAffinoidAlgebra K A) (I : Ideal A) :
    IsAffinoidAlgebra K (A ⧸ I) :=
  hA.of_surjective (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ_surjective K I)

end IsAffinoidAlgebra

end TauCeti
