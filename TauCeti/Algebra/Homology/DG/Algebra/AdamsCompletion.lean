/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.RingTheory.GradedAlgebra.Completion

/-!
# The Adams completion of a bigraded differential graded algebra

Let `A` be a differential graded algebra over a commutative ring `R`, with cohomological grading
`𝒞 : ℤ → Submodule R A` and differential `d`, and let `𝒜 : ℕ → Submodule R A` be a second,
nonnegative **Adams grading** of the underlying algebra which the differential preserves.  For the
two-dimensional Ginzburg algebra of a quiver the Adams grading is the weighted path-length grading
in which the doubled arrows have weight `1` and the adjoined loops weight `2`, and the differential
has bidegree `(1, 0)`.

The **Adams completion** of `A` is its completion along the Adams grading taken in the category of
graded modules: in each cohomological degree `p` the piece `𝒞 p` is completed along the Adams
grading, and the completed algebra is the direct sum over `p` of these completions.  Concretely,
an element is a formal power series over `A` whose coefficient of index `n` is Adams-homogeneous
of degree `n` and whose coefficients have uniformly bounded cohomological degree; the product is
the Cauchy product.  The differential extends coefficientwise, and the completed object is again a
differential graded algebra.  The series with finitely many nonzero coefficients form the image of
`A` under the comparison morphism of differential graded algebras from the ordinary to the
completed algebra.

Bounding the cohomological degree is what makes the completion a *graded* algebra in the
direct-sum sense.  It lies inside the completion `TauCeti.gradedCompletion 𝒜` of the ungraded
algebra along the Adams grading, which imposes no such bound, so the inclusion can be strict.

The two gradings are used through two compatibility conditions, `SetLike.IsHomogeneous 𝒜 (𝒞 p)`
and `SetLike.IsHomogeneous 𝒞 (𝒜 n)`: the components for one grading of an element homogeneous
for the other are again homogeneous.  Both hold when `A` has a basis of simultaneously homogeneous
elements, as a path algebra does.  Only the results which need them assume them.

## Main definitions

* `TauCeti.adamsCompletionPiece`: the series with Adams-homogeneous coefficients all of
  cohomological degree `p`.
* `TauCeti.adamsCompletion`: the Adams completion, as a subalgebra of `PowerSeries A`.
* `TauCeti.adamsCompletionGrading`: its cohomological grading, a `GradedAlgebra`.
* `TauCeti.adamsCompletionDifferential`: the coefficientwise extension of the differential.
* `TauCeti.toAdamsCompletion`: the comparison morphism of differential graded algebras from `A`
  to its Adams completion.

## Main results

* `TauCeti.mem_adamsCompletion_iff`: **an element of the Adams completion is a series with
  Adams-homogeneous coefficients of uniformly bounded cohomological degree.**
* `TauCeti.isDGAlgebra_adamsCompletionDifferential`: **the Adams completion is a differential
  graded algebra.**
* `TauCeti.toAdamsCompletion_injective` and `TauCeti.mem_range_toAdamsCompletion_iff`: the
  comparison morphism is injective, and its image consists of the series with finitely many
  nonzero coefficients.
* `TauCeti.adamsCompletion_le_gradedCompletion`: the Adams completion lies in the completion of
  the ungraded algebra along the Adams grading.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 6, for the completed Ginzburg algebra,
  the completion of the graded path algebra with respect to path length.
* T. Etgü and Y. Lekili, *Koszul duality patterns in Floer theory*, Section 4, for the completed
  and the non-completed two-dimensional Ginzburg algebra.
-/

public section

open DirectSum PowerSeries

namespace TauCeti

section Semiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (𝒞 : ℤ → Submodule R A) [GradedAlgebra 𝒞]

/-! ### The homogeneous pieces -/

/-- The formal power series over `A` whose coefficient of index `n` is Adams-homogeneous of degree
`n` and cohomologically homogeneous of degree `p`: the degree-`p` piece of the Adams completion. -/
def adamsCompletionPiece (p : ℤ) : Submodule R (PowerSeries A) where
  carrier := {f | ∀ n, coeff n f ∈ 𝒜 n ∧ coeff n f ∈ 𝒞 p}
  add_mem' {f g} hf hg n := by
    rw [map_add]
    exact ⟨add_mem (hf n).1 (hg n).1, add_mem (hf n).2 (hg n).2⟩
  zero_mem' n := by
    rw [map_zero]
    exact ⟨zero_mem _, zero_mem _⟩
  smul_mem' r f hf n := by
    rw [coeff_smul]
    exact ⟨Submodule.smul_mem _ r (hf n).1, Submodule.smul_mem _ r (hf n).2⟩

omit [GradedAlgebra 𝒜] [GradedAlgebra 𝒞] in
@[simp]
theorem mem_adamsCompletionPiece_iff {p : ℤ} {f : PowerSeries A} :
    f ∈ adamsCompletionPiece 𝒜 𝒞 p ↔ ∀ n, coeff n f ∈ 𝒜 n ∧ coeff n f ∈ 𝒞 p :=
  Iff.rfl

omit [GradedAlgebra 𝒞] in
/-- Every homogeneous piece lies in the completion of the ungraded algebra along the Adams
grading. -/
theorem adamsCompletionPiece_le_gradedCompletion (p : ℤ) :
    adamsCompletionPiece 𝒜 𝒞 p ≤ Subalgebra.toSubmodule (gradedCompletion 𝒜) := fun _ hf =>
  (Subalgebra.mem_toSubmodule _).2 <| (mem_gradedCompletion_iff 𝒜).2 fun n => (hf n).1

/-- The unit is a series of cohomological degree `0`. -/
theorem one_mem_adamsCompletionPiece_zero : (1 : PowerSeries A) ∈ adamsCompletionPiece 𝒜 𝒞 0 :=
  (mem_adamsCompletionPiece_iff 𝒜 𝒞).2 fun n => by
    rw [coeff_one]
    split_ifs with h
    · subst h
      exact ⟨SetLike.one_mem_graded 𝒜, SetLike.one_mem_graded 𝒞⟩
    · exact ⟨zero_mem _, zero_mem _⟩

/-- **The Cauchy product adds cohomological degrees.** -/
theorem mul_mem_adamsCompletionPiece {p q : ℤ} {f g : PowerSeries A}
    (hf : f ∈ adamsCompletionPiece 𝒜 𝒞 p) (hg : g ∈ adamsCompletionPiece 𝒜 𝒞 q) :
    f * g ∈ adamsCompletionPiece 𝒜 𝒞 (p + q) :=
  (mem_adamsCompletionPiece_iff 𝒜 𝒞).2 fun n => by
    rw [coeff_mul]
    refine ⟨Submodule.sum_mem _ fun ij hij => ?_,
      Submodule.sum_mem _ fun ij _ => SetLike.mul_mem_graded (hf ij.1).2 (hg ij.2).2⟩
    rw [← Finset.mem_antidiagonal.mp hij]
    exact SetLike.mul_mem_graded (hf ij.1).1 (hg ij.2).1

/-! ### The completion -/

/-- **The Adams completion of a bigraded algebra**: the subalgebra of formal power series over
`A` spanned by the homogeneous pieces `TauCeti.adamsCompletionPiece`.  Its elements are the
series with Adams-homogeneous coefficients of uniformly bounded cohomological degree, the direct
sum over the cohomological degree `p` of the completions of the pieces `𝒞 p` along the Adams
grading. -/
noncomputable def adamsCompletion : Subalgebra R (PowerSeries A) :=
  (⨆ p, adamsCompletionPiece 𝒜 𝒞 p).toSubalgebra
    (Submodule.mem_iSup_of_mem 0 (one_mem_adamsCompletionPiece_zero 𝒜 𝒞)) fun f g hf hg => by
      refine Submodule.iSup_induction _
        (motive := fun f => f * g ∈ ⨆ p, adamsCompletionPiece 𝒜 𝒞 p) hf ?_ ?_ ?_
      · intro p f hf
        refine Submodule.iSup_induction _
          (motive := fun g => f * g ∈ ⨆ p, adamsCompletionPiece 𝒜 𝒞 p) hg ?_ ?_ ?_
        · intro q g hg
          exact Submodule.mem_iSup_of_mem (p + q) (mul_mem_adamsCompletionPiece 𝒜 𝒞 hf hg)
        · rw [mul_zero]
          exact zero_mem _
        · intro g₁ g₂ h₁ h₂
          rw [mul_add]
          exact add_mem h₁ h₂
      · rw [zero_mul]
        exact zero_mem _
      · intro f₁ f₂ h₁ h₂
        rw [add_mul]
        exact add_mem h₁ h₂

/-- The Adams completion is spanned by its homogeneous pieces. -/
theorem mem_adamsCompletion_iff_mem_iSup {f : PowerSeries A} :
    f ∈ adamsCompletion 𝒜 𝒞 ↔ f ∈ ⨆ p, adamsCompletionPiece 𝒜 𝒞 p :=
  Iff.rfl

theorem adamsCompletionPiece_le_adamsCompletion (p : ℤ) :
    adamsCompletionPiece 𝒜 𝒞 p ≤ Subalgebra.toSubmodule (adamsCompletion 𝒜 𝒞) := fun _ hf =>
  (Subalgebra.mem_toSubmodule _).2 <|
    (mem_adamsCompletion_iff_mem_iSup 𝒜 𝒞).2 (Submodule.mem_iSup_of_mem p hf)

/-- **The Adams completion lies in the completion of the ungraded algebra along the Adams
grading.**  The ungraded completion imposes no uniform bound on the cohomological degrees of the
coefficients, so the inclusion can be strict. -/
theorem adamsCompletion_le_gradedCompletion : adamsCompletion 𝒜 𝒞 ≤ gradedCompletion 𝒜 :=
  fun _ hf =>
    Submodule.iSup_induction _ (motive := fun f => f ∈ gradedCompletion 𝒜)
      ((mem_adamsCompletion_iff_mem_iSup 𝒜 𝒞).1 hf)
      (fun p _ hf => (Subalgebra.mem_toSubmodule _).1
        (adamsCompletionPiece_le_gradedCompletion 𝒜 𝒞 p hf))
      (zero_mem _) fun _ _ => add_mem

/-- The coefficients of an element of the Adams completion are Adams-homogeneous. -/
theorem coeff_mem_of_mem_adamsCompletion {f : PowerSeries A} (hf : f ∈ adamsCompletion 𝒜 𝒞)
    (n : ℕ) : coeff n f ∈ 𝒜 n :=
  (mem_gradedCompletion_iff 𝒜).1 (adamsCompletion_le_gradedCompletion 𝒜 𝒞 hf) n

/-- **An element of the Adams completion is a series with Adams-homogeneous coefficients of
uniformly bounded cohomological degree.**  The converse direction needs the Adams-homogeneous
pieces to be closed under cohomological projection. -/
theorem mem_adamsCompletion_iff (hc : ∀ n, SetLike.IsHomogeneous 𝒞 (𝒜 n)) {f : PowerSeries A} :
    f ∈ adamsCompletion 𝒜 𝒞 ↔
      (∀ n, coeff n f ∈ 𝒜 n) ∧
        ∃ s : Finset ℤ, ∀ n, ∀ p ∉ s, (decompose 𝒞 (coeff n f) p : A) = 0 := by
  classical
  constructor
  · intro hf
    refine ⟨coeff_mem_of_mem_adamsCompletion 𝒜 𝒞 hf, ?_⟩
    refine Submodule.iSup_induction _
      (motive := fun f => ∃ s : Finset ℤ, ∀ n, ∀ p ∉ s, (decompose 𝒞 (coeff n f) p : A) = 0)
      ((mem_adamsCompletion_iff_mem_iSup 𝒜 𝒞).1 hf) ?_ ?_ ?_
    · intro p f hf
      exact ⟨{p}, fun n q hq =>
        decompose_of_mem_ne 𝒞 (hf n).2 fun h => hq (Finset.mem_singleton.2 h.symm)⟩
    · exact ⟨∅, fun n p _ => by
        rw [map_zero, decompose_zero, DirectSum.zero_apply, Submodule.coe_zero]⟩
    · rintro f g ⟨s, hs⟩ ⟨t, ht⟩
      refine ⟨s ∪ t, fun n p hp => ?_⟩
      rw [Finset.mem_union, not_or] at hp
      rw [map_add, decompose_add, DirectSum.add_apply, Submodule.coe_add, hs n p hp.1,
        ht n p hp.2, add_zero]
  · rintro ⟨hf, s, hs⟩
    -- `f` is the sum over `p ∈ s` of its cohomological components `fᵖ`, each of which lies in the
    -- degree-`p` piece.
    have hfp : ∀ p, PowerSeries.mk (fun n => (decompose 𝒞 (coeff n f) p : A)) ∈
        adamsCompletionPiece 𝒜 𝒞 p := fun p =>
      (mem_adamsCompletionPiece_iff 𝒜 𝒞).2 fun n => by
        rw [coeff_mk]
        exact ⟨hc n p (hf n), SetLike.coe_mem _⟩
    have hsum : f = ∑ p ∈ s, PowerSeries.mk fun n => (decompose 𝒞 (coeff n f) p : A) := by
      ext n
      rw [map_sum]
      simp only [coeff_mk]
      have hsub : (decompose 𝒞 (coeff n f)).support ⊆ s := fun p hp => by
        by_contra hps
        exact DFinsupp.mem_support_iff.1 hp (Subtype.ext (hs n p hps))
      exact (sum_support_decompose 𝒞 (coeff n f)).symm.trans
        (Finset.sum_subset hsub fun p _ hp => by
          rw [DFinsupp.notMem_support_iff.1 hp, Submodule.coe_zero])
    rw [hsum, mem_adamsCompletion_iff_mem_iSup]
    exact Submodule.sum_mem _ fun p _ => Submodule.mem_iSup_of_mem p (hfp p)

end Semiring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (𝒞 : ℤ → Submodule R A) [GradedAlgebra 𝒞]

/-! ### The cohomological grading -/

/-- The degree-`p` piece of the Adams completion, as a submodule of the completion. -/
noncomputable def adamsCompletionGrading (p : ℤ) : Submodule R (adamsCompletion 𝒜 𝒞) :=
  (adamsCompletionPiece 𝒜 𝒞 p).comap (adamsCompletion 𝒜 𝒞).val.toLinearMap

@[simp]
theorem mem_adamsCompletionGrading_iff {p : ℤ} {f : adamsCompletion 𝒜 𝒞} :
    f ∈ adamsCompletionGrading 𝒜 𝒞 p ↔ (f : PowerSeries A) ∈ adamsCompletionPiece 𝒜 𝒞 p :=
  Iff.rfl

/-- Every element of the Adams completion is a finite sum of cohomologically homogeneous ones. -/
theorem iSup_adamsCompletionGrading_eq_top : ⨆ p, adamsCompletionGrading 𝒜 𝒞 p = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨f, hf⟩ := f
  refine Submodule.iSup_induction' (adamsCompletionPiece 𝒜 𝒞)
    (motive := fun g hg => (⟨g, hg⟩ : adamsCompletion 𝒜 𝒞) ∈ ⨆ p, adamsCompletionGrading 𝒜 𝒞 p)
    ?_ ?_ ?_ ((mem_adamsCompletion_iff_mem_iSup 𝒜 𝒞).1 hf)
  · intro p g hg
    exact Submodule.mem_iSup_of_mem p ((mem_adamsCompletionGrading_iff 𝒜 𝒞).2 hg)
  · exact zero_mem _
  · intro g₁ g₂ _ _ h₁ h₂
    exact add_mem h₁ h₂

/-- The homogeneous pieces of the Adams completion are independent, coefficient by coefficient
from the independence of the cohomological grading of `A`. -/
theorem iSupIndep_adamsCompletionGrading : iSupIndep (adamsCompletionGrading 𝒜 𝒞) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum p hp
  have h𝒞 := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero 𝒞).1
    (DirectSum.Decomposition.isInternal 𝒞).submodule_iSupIndep
  apply Subtype.ext
  ext n
  rw [Subalgebra.coe_zero, map_zero]
  refine h𝒞 s (fun q => coeff n (v q : PowerSeries A))
    (fun q hq => ((mem_adamsCompletionGrading_iff 𝒜 𝒞).1 (hv q hq) n).2) ?_ p hp
  rw [← map_sum, ← AddSubmonoidClass.coe_finsetSum, hsum, Subalgebra.coe_zero, map_zero]

/-- The homogeneous pieces form an internal direct sum decomposition of the Adams completion. -/
theorem isInternal_adamsCompletionGrading : DirectSum.IsInternal (adamsCompletionGrading 𝒜 𝒞) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_adamsCompletionGrading 𝒜 𝒞, iSup_adamsCompletionGrading_eq_top 𝒜 𝒞⟩

/-- **The Adams completion is a graded algebra** for the cohomological grading. -/
noncomputable instance instGradedAlgebraAdamsCompletionGrading :
    GradedAlgebra (adamsCompletionGrading 𝒜 𝒞) :=
  { (isInternal_adamsCompletionGrading 𝒜 𝒞).chooseDecomposition with
    one_mem := by
      rw [mem_adamsCompletionGrading_iff, Subalgebra.coe_one]
      exact one_mem_adamsCompletionPiece_zero 𝒜 𝒞
    mul_mem := fun _ _ _ _ hf hg => by
      rw [mem_adamsCompletionGrading_iff, Subalgebra.coe_mul]
      exact mul_mem_adamsCompletionPiece 𝒜 𝒞 hf hg }

/-! ### The differential -/

variable {d : A →ₗ[R] A}

/-- Applying an Adams-preserving differential coefficientwise preserves the Adams completion. -/
theorem mk_map_coeff_mem_adamsCompletion (h : IsDGAlgebra 𝒞 d)
    (hd : ∀ (n : ℕ) ⦃a : A⦄, a ∈ 𝒜 n → d a ∈ 𝒜 n) {f : PowerSeries A}
    (hf : f ∈ adamsCompletion 𝒜 𝒞) :
    PowerSeries.mk (fun n => d (coeff n f)) ∈ adamsCompletion 𝒜 𝒞 := by
  rw [mem_adamsCompletion_iff_mem_iSup] at hf ⊢
  refine Submodule.iSup_induction _
    (motive := fun f => PowerSeries.mk (fun n => d (coeff n f)) ∈ ⨆ p, adamsCompletionPiece 𝒜 𝒞 p)
    hf ?_ ?_ ?_
  · intro p f hf
    refine Submodule.mem_iSup_of_mem (p + 1) ((mem_adamsCompletionPiece_iff 𝒜 𝒞).2 fun n => ?_)
    rw [coeff_mk]
    exact ⟨hd n (hf n).1, h.map_mem (hf n).2⟩
  · have : PowerSeries.mk (fun n => d (coeff n (0 : PowerSeries A))) = 0 :=
      PowerSeries.ext fun n => by simp only [coeff_mk, map_zero]
    rw [this]
    exact zero_mem _
  · intro f g hf hg
    have : PowerSeries.mk (fun n => d (coeff n (f + g))) =
        PowerSeries.mk (fun n => d (coeff n f)) + PowerSeries.mk fun n => d (coeff n g) :=
      PowerSeries.ext fun n => by rw [coeff_mk, map_add, map_add, map_add, coeff_mk, coeff_mk]
    rw [this]
    exact add_mem hf hg

variable (h : IsDGAlgebra 𝒞 d) (hd : ∀ (n : ℕ) ⦃a : A⦄, a ∈ 𝒜 n → d a ∈ 𝒜 n)

/-- **The differential of the Adams completion**: the coefficientwise extension of an
Adams-preserving differential of `A`. -/
noncomputable def adamsCompletionDifferential : adamsCompletion 𝒜 𝒞 →ₗ[R] adamsCompletion 𝒜 𝒞 where
  toFun f := ⟨PowerSeries.mk fun n => d (coeff n (f : PowerSeries A)),
    mk_map_coeff_mem_adamsCompletion 𝒜 𝒞 h hd f.2⟩
  map_add' f g := Subtype.ext <| PowerSeries.ext fun n => by
    simp only [coeff_mk, Subalgebra.coe_add, map_add]
  map_smul' r f := Subtype.ext <| PowerSeries.ext fun n => by
    simp only [coeff_mk, Subalgebra.coe_smul, coeff_smul, map_smul, RingHom.id_apply]

@[simp]
theorem coeff_adamsCompletionDifferential (f : adamsCompletion 𝒜 𝒞) (n : ℕ) :
    coeff n (adamsCompletionDifferential 𝒜 𝒞 h hd f : PowerSeries A) =
      d (coeff n (f : PowerSeries A)) :=
  coeff_mk n fun n => d (coeff n (f : PowerSeries A))

/-- **The Adams completion of a differential graded algebra is a differential graded algebra**:
the coefficientwise differential raises the cohomological degree by one, squares to zero, and
satisfies the graded Leibniz rule for the Cauchy product. -/
theorem isDGAlgebra_adamsCompletionDifferential :
    IsDGAlgebra (adamsCompletionGrading 𝒜 𝒞) (adamsCompletionDifferential 𝒜 𝒞 h hd) where
  map_mem {p f} hf := by
    rw [mem_adamsCompletionGrading_iff] at hf ⊢
    refine (mem_adamsCompletionPiece_iff 𝒜 𝒞).2 fun n => ?_
    rw [coeff_adamsCompletionDifferential]
    exact ⟨hd n (hf n).1, h.map_mem (hf n).2⟩
  sq_zero f := Subtype.ext <| PowerSeries.ext fun n => by
    rw [coeff_adamsCompletionDifferential, coeff_adamsCompletionDifferential, h.sq_zero,
      Subalgebra.coe_zero, map_zero]
  leibniz {p f} hf g := by
    have hf' := (mem_adamsCompletionGrading_iff 𝒜 𝒞).1 hf
    -- the Leibniz rule for each coefficient of the Cauchy product, as an identity in `A`
    have key (n : ℕ) : d (coeff n ((f : PowerSeries A) * (g : PowerSeries A))) =
        coeff n ((adamsCompletionDifferential 𝒜 𝒞 h hd f : PowerSeries A) * (g : PowerSeries A)) +
          p.negOnePow • coeff n ((f : PowerSeries A) *
            (adamsCompletionDifferential 𝒜 𝒞 h hd g : PowerSeries A)) := by
      simp only [coeff_mul, map_sum, coeff_adamsCompletionDifferential, Finset.smul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ij _ => h.leibniz (hf' ij.1).2 _
    -- the identity in the completion is the coefficientwise one after unfolding the coercions
    refine Subtype.ext (PowerSeries.ext fun n => ?_)
    simpa only [coeff_adamsCompletionDifferential, Subalgebra.coe_add, Subalgebra.coe_mul,
      Subalgebra.coe_smul, Units.smul_def, map_add, map_zsmul] using key n

/-! ### The comparison morphism -/

omit [GradedAlgebra 𝒞] in
/-- The series of Adams components of a cohomologically homogeneous element lies in the piece of
its degree. -/
theorem gradedComponentSeries_mem_adamsCompletionPiece (hc : ∀ p, SetLike.IsHomogeneous 𝒜 (𝒞 p))
    {p : ℤ} {a : A} (ha : a ∈ 𝒞 p) :
    gradedComponentSeries 𝒜 a ∈ adamsCompletionPiece 𝒜 𝒞 p :=
  (mem_adamsCompletionPiece_iff 𝒜 𝒞).2 fun n => by
    rw [coeff_gradedComponentSeries]
    exact ⟨SetLike.coe_mem _, hc p n ha⟩

/-- The series of Adams components of every element of `A` lies in the Adams completion. -/
theorem gradedComponentSeries_mem_adamsCompletion (hc : ∀ p, SetLike.IsHomogeneous 𝒜 (𝒞 p))
    (a : A) :
    gradedComponentSeries 𝒜 a ∈ adamsCompletion 𝒜 𝒞 := by
  classical
  rw [mem_adamsCompletion_iff_mem_iSup, ← sum_support_decompose 𝒞 a, map_sum]
  exact Submodule.sum_mem _ fun p _ => Submodule.mem_iSup_of_mem p
    (gradedComponentSeries_mem_adamsCompletionPiece 𝒜 𝒞 hc (SetLike.coe_mem _))

variable (hc : ∀ p, SetLike.IsHomogeneous 𝒜 (𝒞 p))

/-- **The comparison morphism from a bigraded differential graded algebra to its Adams
completion**, sending an element to the series of its Adams-homogeneous components. -/
noncomputable def toAdamsCompletion :
    DGAlgHom h (isDGAlgebra_adamsCompletionDifferential 𝒜 𝒞 h hd) where
  toAlgHom := (gradedComponentSeries 𝒜).codRestrict (adamsCompletion 𝒜 𝒞)
    (gradedComponentSeries_mem_adamsCompletion 𝒜 𝒞 hc)
  map_mem ha := (mem_adamsCompletionGrading_iff 𝒜 𝒞).2
    (gradedComponentSeries_mem_adamsCompletionPiece 𝒜 𝒞 hc ha)
  map_d' a := Subtype.ext <| PowerSeries.ext fun n => by
    rw [coeff_adamsCompletionDifferential, GradedAlgHom.coe_mk]
    simp only [AlgHom.coe_codRestrict, coeff_gradedComponentSeries]
    exact DirectSum.map_decompose_shift 𝒜 𝒜 d id Function.injective_id
      (fun n _ hx => hd n hx) n a

@[simp]
theorem coe_toAdamsCompletion_apply (a : A) :
    ((toAdamsCompletion 𝒜 𝒞 h hd hc a : adamsCompletion 𝒜 𝒞) : PowerSeries A) =
      gradedComponentSeries 𝒜 a :=
  (rfl)

/-- The comparison morphism is injective: a bigraded differential graded algebra embeds in its
Adams completion. -/
theorem toAdamsCompletion_injective : Function.Injective (toAdamsCompletion 𝒜 𝒞 h hd hc) :=
  fun a b hab => gradedComponentSeries_injective 𝒜 (by
    simpa only [coe_toAdamsCompletion_apply] using congrArg Subtype.val hab)

/-- **The image of the comparison morphism consists of the series with finitely many nonzero
coefficients**: the ordinary algebra is the finite-Adams-support part of its completion. -/
theorem mem_range_toAdamsCompletion_iff {f : adamsCompletion 𝒜 𝒞} :
    f ∈ Set.range (toAdamsCompletion 𝒜 𝒞 h hd hc) ↔
      (Function.support fun n => coeff n (f : PowerSeries A)).Finite := by
  have key := mem_range_gradedComponentSeries_iff 𝒜 (f := (f : PowerSeries A))
  rw [AlgHom.mem_range, and_iff_right (coeff_mem_of_mem_adamsCompletion 𝒜 𝒞 f.2)] at key
  rw [Set.mem_range, ← key]
  exact exists_congr fun a => by rw [Subtype.ext_iff, coe_toAdamsCompletion_apply]

end TauCeti
