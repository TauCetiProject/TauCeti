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
arbitrary two-sided ideals in `T₁` proper star rings with separately continuous multiplication.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, §II.5.4.7.
* G. J. Murphy, *C*-Algebras and Operator Theory*, §3.1.
* T. Y. Lam, *Lectures on Modules and Rings*, §3D.
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
  let e' : A ≃+* B := { EquivLike.toEquiv e with map_mul' := map_mul e, map_add' := map_add e }
  have hcomap (J : TwoSidedIdeal B) : e'.mapTwoSidedIdeal.symm J = J.comap e :=
    ext fun _ => (mem_comap e').trans (mem_comap e).symm
  simpa [hcomap] using e'.mapTwoSidedIdeal.symm.forall_inf_eq_bot_iff
    (P := fun J : TwoSidedIdeal B => IsClosed (J : Set B))
    (Q := fun K : TwoSidedIdeal A => IsClosed (K : Set A))
    (fun J hJ => hcomap J ▸ isClosed_comap he.continuous hJ)
    (fun K hK => by
      have hset : (e'.mapTwoSidedIdeal K : Set B) = e '' (K : Set A) := by
        ext b
        refine ⟨fun hb => ⟨e'.symm b, ?_, e'.apply_symm_apply b⟩, ?_⟩
        · simpa [RingEquiv.mapTwoSidedIdeal_apply, mem_comap] using hb
        · rintro ⟨a, ha, rfl⟩
          rw [SetLike.mem_coe, RingEquiv.mapTwoSidedIdeal_apply, mem_comap]
          exact (e'.symm_apply_apply a).symm ▸ ha
      exact hset ▸ he.isClosedMap _ hK)
    (x := I)

end ClosedEssential

section ClosedEssentialRing

variable {A : Type*} [NonUnitalRing A] [TopologicalSpace A]

theorem isClosedEssential_of_annihilator_eq_bot {I : TwoSidedIdeal A}
    (hI : I.annihilator = ⊥) : I.IsClosedEssential :=
  (isEssential_of_annihilator_eq_bot hI).isClosedEssential

theorem isClosedEssential_of_rightAnnihilator_eq_bot {I : TwoSidedIdeal A}
    (hI : I.rightAnnihilator = ⊥) : I.IsClosedEssential :=
  (isEssential_of_rightAnnihilator_eq_bot hI).isClosedEssential

/-- In a `T₁` ring with separately continuous multiplication and proper involution, any two-sided
ideal is essential among closed ideals if and only if its left annihilator is trivial. -/
theorem isClosedEssential_iff_annihilator_eq_bot
    [SeparatelyContinuousMul A] [T1Space A] [StarRing A] [IsProperStar A]
    {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ I.annihilator = ⊥ :=
  ⟨fun h => isClosedEssential_iff.mp h I.annihilator I.isClosed_annihilator
      I.inf_annihilator_eq_bot,
   isClosedEssential_of_annihilator_eq_bot⟩

theorem isClosedEssential_iff_rightAnnihilator_eq_bot
    [SeparatelyContinuousMul A] [T1Space A] [StarRing A] [IsProperStar A]
    {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ I.rightAnnihilator = ⊥ := by
  rw [isClosedEssential_iff_annihilator_eq_bot, I.annihilator_eq_rightAnnihilator]

/-- In a `T₁` ring with separately continuous multiplication and proper involution, essentiality
among closed two-sided ideals and algebraic essentiality coincide for arbitrary two-sided ideals. -/
theorem isClosedEssential_iff_isEssential
    [SeparatelyContinuousMul A] [T1Space A] [StarRing A] [IsProperStar A]
    {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ I.IsEssential := by
  rw [isClosedEssential_iff_annihilator_eq_bot, annihilator_eq_bot_iff_isEssential]

/-- In a `T₁` topological proper star ring, a two-sided ideal is essential exactly when it meets
every nonzero closed two-sided ideal. -/
theorem isEssential_iff_forall_isClosed
    [SeparatelyContinuousMul A] [T1Space A] [StarRing A] [IsProperStar A]
    {I : TwoSidedIdeal A} :
    I.IsEssential ↔ ∀ J : TwoSidedIdeal A, IsClosed (J : Set A) → Disjoint I J → J = ⊥ := by
  rw [← isClosedEssential_iff_isEssential, isClosedEssential_iff]
  simp only [disjoint_iff]

theorem IsClosedEssential.inf
    [SeparatelyContinuousMul A] [T1Space A] [StarRing A] [IsProperStar A]
    {I J : TwoSidedIdeal A} (hI : I.IsClosedEssential) (hJ : J.IsClosedEssential) :
    (I ⊓ J).IsClosedEssential :=
  isClosedEssential_iff_isEssential.mpr
    ((isClosedEssential_iff_isEssential.mp hI).inf (isClosedEssential_iff_isEssential.mp hJ))

@[simp]
theorem isClosedEssential_inf_iff
    [SeparatelyContinuousMul A] [T1Space A] [StarRing A] [IsProperStar A]
    {I J : TwoSidedIdeal A} :
    (I ⊓ J).IsClosedEssential ↔ I.IsClosedEssential ∧ J.IsClosedEssential :=
  ⟨fun h => ⟨h.mono inf_le_left, h.mono inf_le_right⟩, fun ⟨hI, hJ⟩ => hI.inf hJ⟩

@[simp]
theorem isClosedEssential_topologicalClosure_iff
    [IsTopologicalAddGroup A] [SeparatelyContinuousMul A] [T1Space A] [StarRing A]
    [IsProperStar A] {I : TwoSidedIdeal A} :
    I.topologicalClosure.IsClosedEssential ↔ I.IsClosedEssential := by
  rw [isClosedEssential_iff_annihilator_eq_bot, isClosedEssential_iff_annihilator_eq_bot,
    I.annihilator_topologicalClosure]

@[simp]
theorem isEssential_topologicalClosure_iff
    [IsTopologicalAddGroup A] [SeparatelyContinuousMul A] [T1Space A] [StarRing A]
    [IsProperStar A] {I : TwoSidedIdeal A} :
    I.topologicalClosure.IsEssential ↔ I.IsEssential := by
  rw [← isClosedEssential_iff_isEssential, ← isClosedEssential_iff_isEssential,
    isClosedEssential_topologicalClosure_iff]

/-- Pulling back along a ring equivalence between `T₁` proper star rings with separately continuous
multiplication preserves and reflects closed-essentiality. -/
@[simp]
theorem isClosedEssential_comap_iff {B E : Type*} [NonUnitalRing B] [TopologicalSpace B]
    [SeparatelyContinuousMul A] [T1Space A] [StarRing A] [IsProperStar A]
    [SeparatelyContinuousMul B] [T1Space B] [StarRing B] [IsProperStar B]
    [EquivLike E A B] [NonUnitalRingHomClass E A B] (e : E) {I : TwoSidedIdeal B} :
    (I.comap e).IsClosedEssential ↔ I.IsClosedEssential := by
  rw [isClosedEssential_iff_isEssential, isClosedEssential_iff_isEssential, isEssential_comap_iff]

end ClosedEssentialRing

end TwoSidedIdeal
