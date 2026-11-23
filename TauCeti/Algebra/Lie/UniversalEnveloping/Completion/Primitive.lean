/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Bialgebra

import TauCeti.Algebra.DirectSum.Component
import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Injective
import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive
import TauCeti.LinearAlgebra.TensorProduct.Decomposition

/-!
# Completed primitive elements of positively graded universal enveloping algebras

Let `L` be a Lie algebra over a commutative ring `R` equipped with a positive grading `ℒ` by
`(d : PositiveDegrees N)`. Every element in the image of `completedLieToU` is completed primitive.
Conversely, using the internal tensor-product grading of `U(L) ⊗[R] U(L)`, every homogeneous
component of a completed primitive element in `completedEnveloping` is an ordinary primitive
element of `U(L)`. Over a commutative `ℚ`-algebra `R : Type`, combining this componentwise
primitivity with `TauCeti.UniversalEnvelopingAlgebra.primitiveEquiv` identifies the completed
primitive Lie subalgebra of `completedEnveloping` with `d.completedLie ℒ`, without any freeness
or finite-rank hypothesis on `L`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.completedPrimitiveLieEquiv`: Lie isomorphism between
  `d.completedLie ℒ` and `completedPrimitiveLieSubalgebra` over a commutative `ℚ`-algebra.
* `TauCeti.UniversalEnvelopingAlgebra.completedLieExpEquiv`: equivalence between
  `d.completedLie ℒ` and the completed grouplike elements of `completedEnveloping` over a
  commutative `ℚ`-algebra.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_completedLieToU`: every element in the
  image of `completedLieToU` is completed primitive.
* `TauCeti.UniversalEnvelopingAlgebra.isPrimitiveElem_envelopingComponent`: every homogeneous
  enveloping component of a completed primitive element is primitive.
* `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_iff_mem_range_completedLieToU`: over a
  commutative `ℚ`-algebra `R : Type`, the completed primitive elements of `completedEnveloping`
  are precisely the image of `completedLieToU`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV.
* E. Petracci, *Universal representations of Lie algebras by coderivations*,
  arXiv:math/0303020, §8 (used via `TauCeti.UniversalEnvelopingAlgebra.primitiveEquiv` and
  `TauCeti.UniversalEnvelopingAlgebra.ι_injective_of_algebra_rat`).
-/

public section

open scoped TensorProduct DirectSum

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra
open _root_.DirectSum (decompose decompose_sum decompose_of_mem_same decompose_of_mem_ne
  decomposeLinearEquiv)

section CommRing

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "Û" => completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
local notation "𝓕" => degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)

/-- Every element in the image of `completedLieToU` is completed primitive. -/
theorem isCompletedPrimitive_completedLieToU (x : d.completedLie ℒ) :
    IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) (completedLieToU d ℒ x) := by
  rw [isCompletedPrimitive_iff_includeCompletion]
  refine ((𝓕).tensorProduct R 𝓕).completion_ext fun k => ?_
  obtain ⟨y, hy⟩ := (d.degreeIdeal ℒ k).surjective_mkQ
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k x)
  have hrep : (𝓕).projection k (completedLieToU d ℒ x) =
      (𝓕).projection k ((𝓕).toCompletion (ι R y)) := by
    simp only [projection_completedLieToU, ← hy, LieIdeal.mkQ_apply, truncatedLieToU_mk,
      AlgFiltration.projection_toCompletion]
  have hprim := (isCompletedPrimitive_iff_includeCompletion ℒ d.degree _).mp
    (isCompletedPrimitive_toCompletion_ι ℒ d.degree (d.eq_bot_of_degree_neg ℒ) y)
  simpa only [projection_completedCoproduct, map_add,
    AlgFiltration.projection_includeLeftCompletion, AlgFiltration.projection_includeRightCompletion,
    hrep] using congrArg (((𝓕).tensorProduct R 𝓕).projection k) hprim

private def tensorGrading (p : N × N) : Submodule R (U ⊗[R] U) :=
  Submodule.map₂ (TensorProduct.mk R U U)
    (homogeneousSubmodule ℒ p.1) (homogeneousSubmodule ℒ p.2)

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem mul_mem_tensorGrading {p q : N × N} {x y : U ⊗[R] U}
    (hx : x ∈ tensorGrading ℒ p) (hy : y ∈ tensorGrading ℒ q) :
    x * y ∈ tensorGrading ℒ (p + q) :=
  ((Submodule.map₂_tmul_mul_le _ _ _ _).trans <| Submodule.map₂_le_map₂
    (GradedAlgebra.mul_le_grade_add (homogeneousSubmodule ℒ) p.1 q.1)
    (GradedAlgebra.mul_le_grade_add (homogeneousSubmodule ℒ) p.2 q.2))
    (Submodule.mul_mem_mul hx hy)

private def tensorTotalDegree (m : N) : Submodule R (U ⊗[R] U) :=
  ⨆ p : {p : N × N // p.1 + p.2 = m}, tensorGrading ℒ p.1

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem mul_mem_tensorTotalDegree {m₁ m₂ : N} {x y : U ⊗[R] U}
    (hx : x ∈ tensorTotalDegree ℒ m₁) (hy : y ∈ tensorTotalDegree ℒ m₂) :
    x * y ∈ tensorTotalDegree ℒ (m₁ + m₂) := by
  rw [tensorTotalDegree] at hx hy
  refine Submodule.iSup_induction _ (motive := fun x => x * y ∈ tensorTotalDegree ℒ (m₁ + m₂)) hx
    (fun p x hx => ?_) (by simp) (fun _ _ h₁ h₂ => by simpa [add_mul] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun y => x * y ∈ tensorTotalDegree ℒ (m₁ + m₂)) hy
    (fun q y hy => ?_) (by simp) (fun _ _ h₁ h₂ => by simpa [mul_add] using add_mem h₁ h₂)
  refine Submodule.mem_iSup_of_mem ⟨p.1 + q.1, ?_⟩ (mul_mem_tensorGrading ℒ hx hy)
  simp only [Prod.fst_add, Prod.snd_add]; rw [add_add_add_comm, p.2, q.2]

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem comul_mem_tensorTotalDegree {m : N} {a : U} (ha : a ∈ homogeneousSubmodule ℒ m) :
    Coalgebra.comul (R := R) a ∈ tensorTotalDegree ℒ m := by
  refine ((homogeneousSubmodule_le_iff ℒ m
    ((tensorTotalDegree ℒ m).comap (Bialgebra.comulAlgHom R U).toLinearMap)).mpr fun l hl => ?_) ha
  rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, ← hl]; clear ha a hl m
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, map_one, Algebra.TensorProduct.one_def]
    exact Submodule.mem_iSup_of_mem ⟨(0, 0), add_zero 0⟩ (Submodule.apply_mem_map₂
      (TensorProduct.mk R U U) (SetLike.one_mem_graded _) (SetLike.one_mem_graded _))
  | cons b l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul]
    refine mul_mem_tensorTotalDegree ℒ ?_ ih
    rw [Bialgebra.comulAlgHom_apply, comul_ι]
    exact add_mem
      (Submodule.mem_iSup_of_mem ⟨(b.1, 0), add_zero b.1⟩ (Submodule.apply_mem_map₂ _
        (ι_mem_homogeneousSubmodule ℒ b.2.property) (SetLike.one_mem_graded _)))
      (Submodule.mem_iSup_of_mem ⟨(0, b.1), zero_add b.1⟩ (Submodule.apply_mem_map₂ _
        (SetLike.one_mem_graded _) (ι_mem_homogeneousSubmodule ℒ b.2.property)))

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem primDefect_mem_tensorTotalDegree {m : N} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ m) :
    Coalgebra.comul (R := R) a - (1 ⊗ₜ[R] a + a ⊗ₜ[R] 1) ∈ tensorTotalDegree ℒ m :=
  sub_mem (comul_mem_tensorTotalDegree ℒ ha) (add_mem
    (Submodule.mem_iSup_of_mem ⟨(0, m), zero_add m⟩
      (Submodule.apply_mem_map₂ _ (SetLike.one_mem_graded _) ha))
    (Submodule.mem_iSup_of_mem ⟨(m, 0), add_zero m⟩
      (Submodule.apply_mem_map₂ _ ha (SetLike.one_mem_graded _))))

omit [GradedLieAlgebra ℒ] in
private noncomputable def tensorComponentKer
    [_root_.DirectSum.Decomposition (tensorGrading ℒ)] (p : N × N) : Submodule R (U ⊗[R] U) :=
  LinearMap.ker (homogeneousComponent (tensorGrading ℒ) p)

omit [GradedLieAlgebra ℒ] in
private theorem mem_tensorComponentKer
    [_root_.DirectSum.Decomposition (tensorGrading ℒ)] {p : N × N} {z : U ⊗[R] U} :
    z ∈ tensorComponentKer ℒ p ↔ (decompose (tensorGrading ℒ) z p : U ⊗[R] U) = 0 := by
  simp [tensorComponentKer]

omit [GradedLieAlgebra ℒ] in
private theorem decompose_eq_zero_of_mem_tensorTotalDegree
    [_root_.DirectSum.Decomposition (tensorGrading ℒ)] {m : N} {z : U ⊗[R] U}
    (hz : z ∈ tensorTotalDegree ℒ m) {p : N × N} (hp : p.1 + p.2 ≠ m) :
    (decompose (tensorGrading ℒ) z p : U ⊗[R] U) = 0 :=
  (mem_tensorComponentKer ℒ).mp <| (iSup_le fun q _ hw => (mem_tensorComponentKer ℒ).mpr <|
    decompose_of_mem_ne (tensorGrading ℒ) hw fun h => hp (h ▸ q.2) :
      tensorTotalDegree ℒ m ≤ tensorComponentKer ℒ p) hz

private theorem decompose_eq_zero_of_mem_tensorProduct_ideal
    [_root_.DirectSum.Decomposition (tensorGrading ℒ)] {k : ℕ} {t : U ⊗[R] U}
    (ht : t ∈ ((𝓕).tensorProduct R 𝓕).ideal (k + 1))
    {p : N × N} (hp : d.degree p.1 + d.degree p.2 ≤ k) :
    (decompose (tensorGrading ℒ) t p : U ⊗[R] U) = 0 := by
  refine (mem_tensorComponentKer ℒ).mp <| (?_ : tensorFiltrationTail
      (fun n => ((𝓕).ideal n).restrictScalars R) (fun n => ((𝓕).ideal n).restrictScalars R)
      (k + 1) ≤ tensorComponentKer ℒ p) (((𝓕).mem_tensorProduct_ideal_iff R 𝓕).mp ht)
  rw [tensorFiltrationTail_def]; refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  simp only [degreeFiltration_ideal, GradedAlgebra.degreeIdeal_restrictScalars,
    DirectSum.degreeTail_def, Submodule.map₂_iSup_left, Submodule.map₂_iSup_right, iSup_le_iff,
    Submodule.map₂_le]
  intro j hj i hi x hx y hy
  refine (mem_tensorComponentKer ℒ).mpr <| decompose_of_mem_ne (tensorGrading ℒ)
    (i := (i, j)) (Submodule.apply_mem_map₂ (TensorProduct.mk R U U) hx hy) fun heq => ?_
  rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩; omega

private theorem isPrimitiveElem_envelopingComponent_of_mem_monoid {u : Û}
    (hu : IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u) {n : N}
    (hnP : n ∈ d.monoid) : Bialgebra.IsPrimitiveElem R (envelopingComponent d ℒ n u : U) := by
  classical
  let k := (d.degree n).toNat
  let s := (d.finite_cutoff k).toFinset
  let _ : _root_.DirectSum.Decomposition (tensorGrading ℒ) :=
    (_root_.DirectSum.IsInternal.tensorProduct _ _
      (isInternal_homogeneousSubmodule ℒ) (isInternal_homogeneousSubmodule ℒ)).chooseDecomposition
  have hmem := hu.comul_sub_mem_tensorProduct_ideal (mk_sum_envelopingComponent d ℒ k u)
  let δ : U →ₗ[R] U ⊗[R] U :=
    Coalgebra.comul - ((TensorProduct.mk R U U 1) + (TensorProduct.mk R U U).flip 1)
  have hδ (b : U) : δ b = Coalgebra.comul (R := R) b - (1 ⊗ₜ[R] b + b ⊗ₜ[R] 1) := by simp [δ]
  refine Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr (sub_eq_zero.mp ?_)
  apply (decomposeLinearEquiv (tensorGrading ℒ)).injective; rw [map_zero]; ext p
  simp only [_root_.DirectSum.decomposeLinearEquiv_apply, _root_.DirectSum.zero_apply,
    ZeroMemClass.coe_zero]
  by_cases hpn : p.1 + p.2 = n
  · have hpk : d.degree p.1 + d.degree p.2 ≤ k := by rw [← map_add, hpn]; exact Int.self_le_toNat _
    have h0 := decompose_eq_zero_of_mem_tensorProduct_ideal d ℒ hmem hpk
    rw [← hδ _, map_sum δ _ s, decompose_sum, _root_.DirectSum.sum_apply, Submodule.coe_sum,
      Finset.sum_eq_single n] at h0
    · rwa [hδ] at h0
    · exact fun m _ hmn => by
        rw [hδ]; exact decompose_eq_zero_of_mem_tensorTotalDegree ℒ
          (primDefect_mem_tensorTotalDegree ℒ (envelopingComponent d ℒ m u).2)
          (hpn.trans_ne hmn.symm)
    · exact fun hns => (hns (by simp [s, k, hnP])).elim
  · exact decompose_eq_zero_of_mem_tensorTotalDegree ℒ
      (primDefect_mem_tensorTotalDegree ℒ (envelopingComponent d ℒ n u).2) hpn

/-- Every homogeneous enveloping component of a completed primitive element is an ordinary
primitive element of `U(L)`. -/
theorem isPrimitiveElem_envelopingComponent {u : Û}
    (hu : IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u) (n : N) :
    Bialgebra.IsPrimitiveElem R (envelopingComponent d ℒ n u : U) := by
  by_cases hnP : n ∈ d.monoid
  · exact isPrimitiveElem_envelopingComponent_of_mem_monoid d ℒ hu hnP
  · have hc0 : (envelopingComponent d ℒ n u : U) = 0 := (Submodule.mem_bot R).mp <|
      homogeneousSubmodule_eq_bot_of_not_mem_monoid ℒ d hnP ▸ (envelopingComponent d ℒ n u).2
    rw [hc0]; exact (Coalgebra.skewPrimitive R (1 : U) 1).zero_mem

end CommRing

/-! ### Identification of completed primitive elements over `ℚ`-algebras -/

section Rational

universe u v

variable {N : Type u} {R : Type} {L : Type v} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "Û" => completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
local notation "𝓕" => degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedLieToU` is injective without a freeness
hypothesis. -/
theorem completedLieToU_injective_of_algebra_rat : Function.Injective (completedLieToU d ℒ) :=
  completedLieToU_injective d ℒ (ι_injective_of_algebra_rat R L)

/-- Over a commutative `ℚ`-algebra `R : Type`, an element of `completedEnveloping` is completed
primitive if and only if it lies in the image of `completedLieToU`. -/
theorem isCompletedPrimitive_iff_mem_range_completedLieToU (u : Û) :
    IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u ↔
      u ∈ Set.range (completedLieToU d ℒ) := by
  refine ⟨fun hu => ?_, ?_⟩
  · let _ := d.lieRingPi ℒ; let _ := d.lieAlgebraPi ℒ
    let y : N → L := fun n => (primitiveEquiv R L).symm
      ⟨(envelopingComponent d ℒ n u : U), isPrimitiveElem_envelopingComponent d ℒ hu n⟩
    let x : ∀ n, ℒ n := fun n => decompose ℒ (y n) n
    have hx (n : N) : ι R (x n : L) = (envelopingComponent d ℒ n u : U) := by
      have hy : ι R (y n) = (envelopingComponent d ℒ n u : U) := ι_primitiveEquiv_symm R L _
      rw [← coe_decompose_mkAlgHom_ι, ← ι_apply (R := R) (x := y n), hy]
      exact decompose_of_mem_same _ (envelopingComponent d ℒ n u).property
    refine ⟨(d.completionLieEquivPi ℒ).symm x, (𝓕).completion_ext fun k => ?_⟩
    rw [projection_completedLieToU, d.completionProjection_completionLieEquivPi_symm ℒ x k,
      LieIdeal.mkQ_apply, truncatedLieToU_mk, map_sum]
    simp_rw [hx]; exact mk_sum_envelopingComponent d ℒ k u
  · rintro ⟨x, rfl⟩; exact isCompletedPrimitive_completedLieToU d ℒ x

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedLieToU` identifies `d.completedLie ℒ`
with the Lie subalgebra of completed primitive elements in `completedEnveloping`. -/
noncomputable def completedPrimitiveLieEquiv :
    d.completedLie ℒ ≃ₗ⁅R⁆
      completedPrimitiveLieSubalgebra ℒ d.degree (d.eq_bot_of_degree_neg ℒ) :=
  LieEquiv.ofBijective
    { toLinearMap := (completedLieToU d ℒ).toLinearMap.codRestrict
        (completedPrimitiveLieSubalgebra ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).toSubmodule
        fun x => (mem_completedPrimitiveLieSubalgebra_iff _ _ _).mpr
          (isCompletedPrimitive_completedLieToU d ℒ x)
      map_lie' := fun {x y} => Subtype.ext ((completedLieToU d ℒ).map_lie x y) }
    ⟨fun _ _ h => completedLieToU_injective_of_algebra_rat d ℒ (congrArg Subtype.val h), fun u => by
      obtain ⟨x, hx⟩ := (isCompletedPrimitive_iff_mem_range_completedLieToU d ℒ u.1).mp
        ((mem_completedPrimitiveLieSubalgebra_iff _ _ _).mp u.2)
      exact ⟨x, Subtype.ext hx⟩⟩

@[simp]
theorem coe_completedPrimitiveLieEquiv_apply (x : d.completedLie ℒ) :
    (completedPrimitiveLieEquiv d ℒ x : Û) = completedLieToU d ℒ x := (rfl)

@[simp]
theorem completedLieToU_completedPrimitiveLieEquiv_symm
    (u : completedPrimitiveLieSubalgebra ℒ d.degree (d.eq_bot_of_degree_neg ℒ)) :
    completedLieToU d ℒ ((completedPrimitiveLieEquiv d ℒ).symm u) = (u : Û) :=
  congrArg Subtype.val ((completedPrimitiveLieEquiv d ℒ).apply_symm_apply u)

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedExp ∘ completedLieToU` identifies
`d.completedLie ℒ` with the completed grouplike elements of `completedEnveloping`. -/
noncomputable def completedLieExpEquiv :
    d.completedLie ℒ ≃ {u : Û // IsCompletedGroupLike ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u} :=
  (completedPrimitiveLieEquiv d ℒ).toLinearEquiv.toEquiv.trans
    (completedPrimitiveExpEquiv ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ))

@[simp]
theorem coe_completedLieExpEquiv_apply (x : d.completedLie ℒ) :
    (completedLieExpEquiv d ℒ x : Û) =
      (𝓕).completedExp ⟨completedLieToU d ℒ x, completedLieToU_mem_completionIdeal_one d ℒ x⟩ :=
  coe_completedPrimitiveExpEquiv ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ) _

@[simp]
theorem completedLieToU_completedLieExpEquiv_symm
    (u : {u : Û // IsCompletedGroupLike ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u}) :
    completedLieToU d ℒ ((completedLieExpEquiv d ℒ).symm u) =
      (𝓕).completedLog ⟨u.1, u.2.sub_one_mem_completionIdeal_one (d.eq_bot_of_degree_nonpos ℒ)⟩ :=
  (completedLieToU_completedPrimitiveLieEquiv_symm d ℒ _).trans
    (coe_completedPrimitiveExpEquiv_symm ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ) u)

end Rational

end TauCeti.UniversalEnvelopingAlgebra
