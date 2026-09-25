/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Basic API for ideles

This file records the relation between Mathlib's diagonal embeddings into the idele group and the
adele ring. In particular, principal-idele membership can be tested on the underlying adele.

It also defines the finite component `NumberField.IdeleGroup.toFiniteIdele` of an idele, a unit of
the finite adele ring, and the idele `NumberField.IdeleGroup.ofFiniteIdele` with a given finite
component and trivial infinite components.  This is how ideles are handed to and from the
finite-idele theory of fractional ideals: on a principal idele the finite component is the
principal finite idele of the same element.
-/

public section
noncomputable section

open IsDedekindDomain

namespace NumberField.IdeleGroup

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The underlying adele of a principal idele is the diagonal adele of the underlying field
element. -/
@[simp]
theorem coe_unitEmbedding (x : Kˣ) :
    ((unitEmbedding R K x : IdeleGroup R K) : AdeleRing R K) =
      algebraMap K (AdeleRing R K) x :=
  rfl

/-- An idele is principal exactly when its underlying adele lies in the diagonal copy of the
fraction field. -/
-- This is intentionally not a simp lemma: Mathlib's `MonoidHom.mem_range` is already `simp`, so it
-- rewrites this left-hand side to an existential over `unitEmbedding` and the simp-normal-form
-- linter rejects the membership form.
theorem mem_principalSubgroup_iff (x : IdeleGroup R K) :
    x ∈ principalSubgroup R K ↔
      (x : AdeleRing R K) ∈ AdeleRing.principalSubgroup R K := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, coe_unitEmbedding R K y⟩
  · rintro ⟨y, hy⟩
    by_cases hA : Nontrivial (AdeleRing R K)
    · let _ := hA
      have hy0 : y ≠ 0 := by
        intro hyzero
        subst y
        exact x.ne_zero (by simpa using hy.symm)
      refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
      simpa only [coe_unitEmbedding, Units.val_mk0] using hy
    · have _ : Subsingleton (AdeleRing R K) := not_nontrivial_iff_subsingleton.mp hA
      exact ⟨1, Units.ext (Subsingleton.elim _ _)⟩

/-- The finite component of an idele, a unit of the finite adele ring (a *finite idele*). -/
def toFiniteIdele : IdeleGroup R K →* (FiniteAdeleRing R K)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing R K))

@[simp]
theorem coe_toFiniteIdele (x : IdeleGroup R K) :
    (toFiniteIdele R K x : FiniteAdeleRing R K) = (x : AdeleRing R K).2 :=
  (rfl)

/-- The finite component of a principal idele is the principal finite idele of the same
element. -/
@[simp]
theorem toFiniteIdele_unitEmbedding (x : Kˣ) :
    toFiniteIdele R K (unitEmbedding R K x) = FiniteAdeleRing.unitEmbedding R K x :=
  Units.ext (rfl)

/-- The idele with the given finite component and all infinite components equal to `1`. -/
def ofFiniteIdele : (FiniteAdeleRing R K)ˣ →* IdeleGroup R K :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing R K))

@[simp]
theorem coe_ofFiniteIdele (a : (FiniteAdeleRing R K)ˣ) :
    (ofFiniteIdele R K a : AdeleRing R K) =
      ((1 : InfiniteAdeleRing K), (a : FiniteAdeleRing R K)) :=
  (rfl)

/-- The finite component of `ofFiniteIdele R K a` is `a`. -/
@[simp]
theorem toFiniteIdele_ofFiniteIdele (a : (FiniteAdeleRing R K)ˣ) :
    toFiniteIdele R K (ofFiniteIdele R K a) = a :=
  Units.ext (rfl)

/-- The finite component of an idele concentrated at an infinite place is trivial. -/
@[simp]
theorem toFiniteIdele_ofCompletion (w : NumberField.InfinitePlace K) (u : w.Completionˣ) :
    toFiniteIdele R K (ofCompletion R K w u) = 1 :=
  Units.ext (rfl)

end NumberField.IdeleGroup
