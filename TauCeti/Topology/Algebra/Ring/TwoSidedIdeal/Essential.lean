/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal.Annihilator

/-!
# Closed-essential two-sided ideals in topological rings

Two-sided ideals meeting every nonzero closed two-sided ideal (`TwoSidedIdeal.IsClosedEssential`),
lattice/homeomorphism API, and equivalences with `IsEssential` and `annihilator = ⊥` for
`star`-closed ideals in `T₁` proper star rings with separately continuous multiplication.
-/

public section

namespace TwoSidedIdeal

section ClosedEssential

variable {A : Type*} [NonUnitalNonAssocRing A] [TopologicalSpace A]

/-- An arbitrary (not necessarily closed) two-sided ideal `I` of a ring `A` equipped with a
topology is *essential among closed ideals* if it meets every nonzero closed two-sided ideal of `A`
nontrivially. -/
def IsClosedEssential (I : TwoSidedIdeal A) : Prop :=
  ∀ J : TwoSidedIdeal A, IsClosed (J : Set A) → J ≠ ⊥ → I ⊓ J ≠ ⊥

theorem isClosedEssential_def {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ ∀ J : TwoSidedIdeal A, IsClosed (J : Set A) → J ≠ ⊥ → I ⊓ J ≠ ⊥ :=
  (Iff.rfl)

/-- Contrapositive characterization: `I.IsClosedEssential` iff `I ⊓ J = ⊥` forces `J = ⊥` for every
closed two-sided ideal `J`. -/
theorem isClosedEssential_iff {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ ∀ J : TwoSidedIdeal A, IsClosed (J : Set A) → I ⊓ J = ⊥ → J = ⊥ :=
  ⟨fun h J hJ hIJ => by_contra fun hJ0 => h J hJ hJ0 hIJ,
   fun h J hJ hJ0 hIJ => hJ0 (h J hJ hIJ)⟩

theorem IsEssential.isClosedEssential {I : TwoSidedIdeal A} (hI : I.IsEssential) :
    I.IsClosedEssential :=
  isClosedEssential_def.mpr fun J _ => isEssential_def.mp hI J

@[simp]
theorem isClosedEssential_top : (⊤ : TwoSidedIdeal A).IsClosedEssential :=
  isEssential_top.isClosedEssential

theorem IsClosedEssential.mono {I J : TwoSidedIdeal A} (hI : I.IsClosedEssential) (hIJ : I ≤ J) :
    J.IsClosedEssential :=
  isClosedEssential_iff.mpr fun K hK hJK =>
    isClosedEssential_iff.mp hI K hK (le_bot_iff.mp ((inf_le_inf_right K hIJ).trans hJK.le))

theorem IsClosedEssential.inf_of_isClosed {I J : TwoSidedIdeal A}
    (hI : I.IsClosedEssential) (hJ : J.IsClosedEssential) [IsClosed (J : Set A)] :
    (I ⊓ J).IsClosedEssential :=
  isClosedEssential_iff.mpr fun K hK hIJK =>
    isClosedEssential_iff.mp hJ K hK <|
      isClosedEssential_iff.mp hI (J ⊓ K) (isClosed_inf J K) (by rwa [← inf_assoc])

@[simp]
theorem isClosedEssential_bot_iff : (⊥ : TwoSidedIdeal A).IsClosedEssential ↔ Subsingleton A :=
  ⟨fun h => subsingleton_iff.mp <|
      subsingleton_iff_bot_eq_top.mp (isClosedEssential_iff.mp h ⊤ isClosed_top (by simp)).symm,
   fun h => (isEssential_bot_iff.mpr h).isClosedEssential⟩

theorem not_isClosedEssential_bot [Nontrivial A] : ¬ (⊥ : TwoSidedIdeal A).IsClosedEssential := by
  rw [isClosedEssential_bot_iff]
  exact not_subsingleton A

theorem IsClosedEssential.ne_bot [Nontrivial A] {I : TwoSidedIdeal A}
    (hI : I.IsClosedEssential) : I ≠ ⊥ :=
  fun h => not_isClosedEssential_bot (h ▸ hI)

/-- Pulling back along a homeomorphic ring equivalence preserves and reflects
closed-essentiality. -/
theorem isClosedEssential_comap_iff_of_isHomeomorph {B E : Type*} [NonUnitalNonAssocRing B]
    [TopologicalSpace B] [EquivLike E A B] [NonUnitalRingHomClass E A B] (e : E)
    (he : IsHomeomorph e) {I : TwoSidedIdeal B} :
    (I.comap e).IsClosedEssential ↔ I.IsClosedEssential := by
  rw [isClosedEssential_iff, isClosedEssential_iff]
  refine forall_inf_eq_bot_comap_iff e (fun _ hJ => isClosed_comap he.continuous hJ)
    fun K hK J hJK => ?_
  have hset : (J : Set B) = e '' (K : Set A) := by
    have hpre : e ⁻¹' (J : Set B) = (K : Set A) := by
      rw [← hJK]
      exact Set.ext fun _ => (mem_comap e).symm
    rw [← hpre, Set.image_preimage_eq _ (EquivLike.surjective e)]
  exact hset ▸ he.isClosedMap _ hK

end ClosedEssential

section ClosedEssentialRing

variable {A : Type*} [NonUnitalRing A] [TopologicalSpace A]

theorem isClosedEssential_of_annihilator_eq_bot {I : TwoSidedIdeal A}
    (hI : I.annihilator = ⊥) : I.IsClosedEssential :=
  (isEssential_of_annihilator_eq_bot hI).isClosedEssential

theorem isClosedEssential_of_rightAnnihilator_eq_bot {I : TwoSidedIdeal A}
    (hI : I.rightAnnihilator = ⊥) : I.IsClosedEssential :=
  (isEssential_of_rightAnnihilator_eq_bot hI).isClosedEssential

/-- In a `T₁` ring with separately continuous multiplication and proper involution, a `star`-closed
two-sided ideal is essential among closed ideals if and only if its left annihilator is trivial. -/
theorem isClosedEssential_iff_annihilator_eq_bot_of_star_mem
    [SeparatelyContinuousMul A] [T1Space A] [StarRing A] [IsProperStar A]
    {I : TwoSidedIdeal A} (hI : ∀ x ∈ I, star x ∈ I) :
    I.IsClosedEssential ↔ I.annihilator = ⊥ :=
  ⟨fun h => isClosedEssential_iff.mp h I.annihilator I.isClosed_annihilator
      (inf_annihilator hI),
   isClosedEssential_of_annihilator_eq_bot⟩

theorem isClosedEssential_iff_rightAnnihilator_eq_bot_of_star_mem
    [SeparatelyContinuousMul A] [T1Space A] [StarRing A] [IsProperStar A]
    {I : TwoSidedIdeal A} (hI : ∀ x ∈ I, star x ∈ I) :
    I.IsClosedEssential ↔ I.rightAnnihilator = ⊥ := by
  rw [isClosedEssential_iff_annihilator_eq_bot_of_star_mem hI,
    annihilator_eq_rightAnnihilator_of_star_mem hI]

/-- In a `T₁` ring with separately continuous multiplication and proper involution, essentiality
among closed two-sided ideals and algebraic essentiality coincide for `star`-closed two-sided
ideals. -/
theorem isClosedEssential_iff_isEssential_of_star_mem
    [SeparatelyContinuousMul A] [T1Space A] [StarRing A] [IsProperStar A]
    {I : TwoSidedIdeal A} (hI : ∀ x ∈ I, star x ∈ I) :
    I.IsClosedEssential ↔ I.IsEssential := by
  rw [isClosedEssential_iff_annihilator_eq_bot_of_star_mem hI,
    annihilator_eq_bot_iff_isEssential hI]

/-- In a `T₁` topological proper star ring, a self-adjoint ideal is essential exactly when it meets
every nonzero closed two-sided ideal. -/
theorem isEssential_iff_forall_isClosed
    [SeparatelyContinuousMul A] [T1Space A] [StarRing A] [IsProperStar A]
    {I : TwoSidedIdeal A} (hI : ∀ x ∈ I, star x ∈ I) :
    I.IsEssential ↔ ∀ J : TwoSidedIdeal A, IsClosed (J : Set A) → Disjoint I J → J = ⊥ := by
  rw [← isClosedEssential_iff_isEssential_of_star_mem hI, isClosedEssential_iff]
  simp only [disjoint_iff]

end ClosedEssentialRing

end TwoSidedIdeal
