/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Graded.Completion
public import TauCeti.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import TauCeti.RingTheory.FilteredAlgebra.Bialgebra
public import TauCeti.RingTheory.GradedAlgebra.Degree.TensorProduct

/-!
# Degree completions of universal enveloping algebras as completed bialgebras

For a `Γ`-graded Lie algebra `L` over any commutative ring `R`, comultiplication on `U(L)` carries
each total-degree piece `homogeneousSubmodule ℒ n` into the sum of bidegree tensor summands
`U_i ⊗ U_j` with `i + j = n`. Consequently, every nonnegative degree filtration
`UniversalEnvelopingAlgebra.degreeFiltration ℒ d hneg` is a bialgebra filtration
(`AlgFiltration.IsBialgFiltration`), equipping `(degreeFiltration ℒ d hneg).completion` with a
completed coproduct, completed counit, and the Lie subalgebra `completedPrimitives` of completed
primitive elements.

When the Lie grading is positive (`IsPositiveGrading d ℒ`), the canonical Lie map `L → U(L)`
descends to compatible Lie homomorphisms `truncatedLieToU` at every finite cutoff and lifts to a
Lie homomorphism
`completedLieToU : d.completedLie ℒ →ₗ⁅R⁆ (degreeFiltration ℒ d.degree hneg).completion` whose
image consists of completed primitive elements in the first completion ideal. Whenever
`ι R : L → U(L)` is injective, both `truncatedLieToU` and `completedLieToU` are injective.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_isBialgFiltration`: every nonnegative degree
  filtration on a graded enveloping algebra is a bialgebra filtration.
* `TauCeti.UniversalEnvelopingAlgebra.completedPrimitives`: the Lie subalgebra of completed
  primitive elements in `(degreeFiltration ℒ d hneg).completion`.
* `TauCeti.UniversalEnvelopingAlgebra.truncatedLieToU`: the finite-order Lie homomorphism
  `d.truncatedLie ℒ k →ₗ⁅R⁆ U(L) ⧸ F.ideal (k + 1)`.
* `TauCeti.UniversalEnvelopingAlgebra.completedLieToU`: the completed Lie homomorphism
  `d.completedLie ℒ →ₗ⁅R⁆ F.completion`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 1–3, Ch. II, §6 (completed enveloping
  algebras of positively graded Lie algebras and their primitive elements).
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

section Support

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem word_eq_zero_of_not_mem_monoid (d : PositiveDegrees Γ) [IsPositiveGrading d ℒ]
    (l : List (Σ i, ℒ i)) (hl : (l.map Sigma.fst).sum ∉ d.monoid) :
    (l.map fun x => ι R (x.2 : L)).prod = 0 := by
  induction l with
  | nil => exact (hl d.monoid.zero_mem).elim
  | cons a l ih =>
    by_cases ha : a.1 ∈ d.monoid
    · have hsum : (l.map Sigma.fst).sum ∉ d.monoid := fun hs =>
        hl (by simpa only [List.map_cons, List.sum_cons] using d.monoid.add_mem ha hs)
      simp only [List.map_cons, List.prod_cons, ih hsum, mul_zero]
    · have ha0 : (a.2 : L) = 0 := by
        simpa only [IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) a.1 (Or.inl ha), Submodule.mem_bot]
          using a.2.property
      simp only [List.map_cons, List.prod_cons, ha0, map_zero, zero_mul]

/-- When a Lie grading is positive for `d`, every enveloping piece outside `d.monoid` vanishes. -/
theorem homogeneousSubmodule_eq_bot_of_not_mem_monoid (d : PositiveDegrees Γ)
    [IsPositiveGrading d ℒ] {n : Γ} (hn : n ∉ d.monoid) :
    homogeneousSubmodule ℒ n = ⊥ := by
  rw [eq_bot_iff, homogeneousSubmodule_le_iff]
  intro l hl
  rw [Submodule.mem_bot]
  exact word_eq_zero_of_not_mem_monoid ℒ d l (hl ▸ hn)

private def bidegreePiece (p : Γ × Γ) : Submodule R (U ⊗[R] U) :=
  Submodule.map₂ (TensorProduct.mk R U U)
    (homogeneousSubmodule ℒ p.1) (homogeneousSubmodule ℒ p.2)

private def comulHomogeneousSpan (n : Γ) : Submodule R (U ⊗[R] U) :=
  ⨆ p : {p : Γ × Γ // p.1 + p.2 = n}, bidegreePiece ℒ p.1

private theorem mulLeft_ι_tmul_one_mem_bidegreePiece {m i j : Γ} {x : L} (hx : x ∈ ℒ m) :
    bidegreePiece ℒ (i, j) ≤
      (bidegreePiece ℒ (m + i, j)).comap (LinearMap.mulLeft R (ι R x ⊗ₜ[R] (1 : U))) := by
  refine Submodule.map₂_le.mpr fun u hu v hv => ?_
  simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, TensorProduct.mk_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact Submodule.apply_mem_map₂ _
    (SetLike.mul_mem_graded (ι_mem_homogeneousSubmodule ℒ hx) hu) hv

private theorem mulLeft_one_tmul_ι_mem_bidegreePiece {m i j : Γ} {x : L} (hx : x ∈ ℒ m) :
    bidegreePiece ℒ (i, j) ≤
      (bidegreePiece ℒ (i, m + j)).comap (LinearMap.mulLeft R ((1 : U) ⊗ₜ[R] ι R x)) := by
  refine Submodule.map₂_le.mpr fun u hu v hv => ?_
  simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, TensorProduct.mk_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact Submodule.apply_mem_map₂ _ hu
    (SetLike.mul_mem_graded (ι_mem_homogeneousSubmodule ℒ hx) hv)

private theorem comulHomogeneousSpan_le_comap_mulLeft {m n : Γ} {x : L} (hx : x ∈ ℒ m) :
    comulHomogeneousSpan ℒ n ≤
      (comulHomogeneousSpan ℒ (m + n)).comap
        (LinearMap.mulLeft R (ι R x ⊗ₜ[R] (1 : U) + (1 : U) ⊗ₜ[R] ι R x)) := by
  refine iSup_le fun p t ht => ?_
  simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, add_mul]
  have h1 : (ι R x ⊗ₜ[R] (1 : U)) * t ∈ comulHomogeneousSpan ℒ (m + n) :=
    le_iSup (fun q : {q : Γ × Γ // q.1 + q.2 = m + n} => bidegreePiece ℒ q.1)
      ⟨(m + p.1.1, p.1.2), by rw [add_assoc, p.2]⟩
      (mulLeft_ι_tmul_one_mem_bidegreePiece ℒ hx ht)
  have h2 : ((1 : U) ⊗ₜ[R] ι R x) * t ∈ comulHomogeneousSpan ℒ (m + n) :=
    le_iSup (fun q : {q : Γ × Γ // q.1 + q.2 = m + n} => bidegreePiece ℒ q.1)
      ⟨(p.1.1, m + p.1.2), by rw [add_left_comm, p.2]⟩
      (mulLeft_one_tmul_ι_mem_bidegreePiece ℒ hx ht)
  exact add_mem h1 h2

private theorem comul_prod_mem_comulHomogeneousSpan (l : List (Σ i, ℒ i)) :
    Coalgebra.comul (R := R) (l.map fun x => ι R (x.2 : L)).prod ∈
      comulHomogeneousSpan ℒ (l.map Sigma.fst).sum := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, Bialgebra.comul_one]
    exact le_iSup (fun q : {q : Γ × Γ // q.1 + q.2 = 0} => bidegreePiece ℒ q.1)
      ⟨(0, 0), add_zero 0⟩
      (Submodule.apply_mem_map₂ _
        (SetLike.one_mem_graded (homogeneousSubmodule ℒ))
        (SetLike.one_mem_graded (homogeneousSubmodule ℒ)))
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Bialgebra.comul_mul, comul_ι]
    exact comulHomogeneousSpan_le_comap_mulLeft ℒ a.2.property ih

private theorem comul_mem_comulHomogeneousSpan {n : Γ} {u : U}
    (hu : u ∈ homogeneousSubmodule ℒ n) :
    Coalgebra.comul (R := R) u ∈ comulHomogeneousSpan ℒ n := by
  have hle : homogeneousSubmodule ℒ n ≤
      (comulHomogeneousSpan ℒ n).comap (Coalgebra.comul (R := R)) := by
    rw [homogeneousSubmodule_le_iff]
    rintro l rfl
    exact comul_prod_mem_comulHomogeneousSpan ℒ l
  exact hle hu

end Support

section GradedBialgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) [DecidableEq Γ] [GradedLieAlgebra ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- On an enveloping element of homogeneous degree `n`, every bidegree projection of `Δ(u)` with
`i + j ≠ n` vanishes. -/
theorem map_proj_comul_eq_zero_of_mem {n : Γ} {u : U}
    (hu : u ∈ homogeneousSubmodule ℒ n) {i j : Γ} (hij : i + j ≠ n) :
    TensorProduct.map (_root_.GradedAlgebra.proj (homogeneousSubmodule ℒ) i)
      (_root_.GradedAlgebra.proj (homogeneousSubmodule ℒ) j)
      (Coalgebra.comul (R := R) u) = 0 := by
  have hker : comulHomogeneousSpan ℒ n ≤
      LinearMap.ker (TensorProduct.map (_root_.GradedAlgebra.proj (homogeneousSubmodule ℒ) i)
        (_root_.GradedAlgebra.proj (homogeneousSubmodule ℒ) j)) := by
    refine iSup_le fun p t ht => LinearMap.mem_ker.mpr ?_
    exact TauCeti.GradedAlgebra.tensorProduct_proj_eq_zero_of_mem
      (homogeneousSubmodule ℒ) (homogeneousSubmodule ℒ) ht fun hp =>
        hij (by simpa only [hp] using p.2)
  exact LinearMap.mem_ker.mp (hker (comul_mem_comulHomogeneousSpan ℒ hu))

/-- The `(i, j)`-bidegree projection of `Δ(u)` depends only on the `(i + j)`-homogeneous component
of `u`. -/
theorem map_proj_comul (u : U) (i j : Γ) :
    TensorProduct.map (_root_.GradedAlgebra.proj (homogeneousSubmodule ℒ) i)
      (_root_.GradedAlgebra.proj (homogeneousSubmodule ℒ) j)
      (Coalgebra.comul (R := R) u) =
    TensorProduct.map (_root_.GradedAlgebra.proj (homogeneousSubmodule ℒ) i)
      (_root_.GradedAlgebra.proj (homogeneousSubmodule ℒ) j)
      (Coalgebra.comul (R := R)
        (DirectSum.decompose (homogeneousSubmodule ℒ) u (i + j) : U)) := by
  induction u using _root_.DirectSum.Decomposition.inductionOn (homogeneousSubmodule ℒ) with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | @homogeneous m x =>
    by_cases hm : m = i + j
    · subst hm
      rw [_root_.DirectSum.decompose_of_mem_same (homogeneousSubmodule ℒ) x.property]
    · rw [map_proj_comul_eq_zero_of_mem ℒ x.property (Ne.symm hm),
        _root_.DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ) x.property hm]
      simp

/-- The enveloping degree filtration agrees with `GradedAlgebra.degreeFiltration` on
`homogeneousSubmodule ℒ`. -/
theorem degreeFiltration_eq_gradedAlgebra_degreeFiltration (d : Γ →+ ℤ)
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    degreeFiltration ℒ d hneg =
      TauCeti.GradedAlgebra.degreeFiltration (homogeneousSubmodule ℒ) d
        (fun _ hn => homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg hn) :=
  AlgFiltration.ext <| funext fun k => by
    rw [degreeFiltration_ideal, TauCeti.GradedAlgebra.degreeFiltration_ideal]

/-- Comultiplication preserves every nonnegative degree filtration on a graded enveloping algebra.
-/
theorem degreeFiltration_ideal_le_comap_comul (d : Γ →+ ℤ)
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    (degreeFiltration ℒ d hneg).ideal k ≤
      (((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).ideal k).comap (Bialgebra.comulAlgHom R U) := by
  intro u hu
  rw [Ideal.mem_comap, Bialgebra.comulAlgHom_apply,
    degreeFiltration_eq_gradedAlgebra_degreeFiltration ℒ d hneg,
    TauCeti.GradedAlgebra.mem_tensorProduct_degreeFiltration_ideal_iff]
  intro i j hij
  rw [map_proj_comul]
  have hu0 : (DirectSum.decompose (homogeneousSubmodule ℒ) u (i + j) : U) = 0 :=
    (mem_degreeFiltration_ideal_iff ℒ d hneg).mp hu (i + j) (by simpa only [map_add] using hij)
  simp [hu0]

/-- Every nonnegative degree filtration on a graded enveloping algebra is a bialgebra filtration.
-/
instance degreeFiltration_isBialgFiltration (d : Γ →+ ℤ)
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    (degreeFiltration ℒ d hneg).IsBialgFiltration R where
  ideal_le_comap_comul := degreeFiltration_ideal_le_comap_comul ℒ d hneg
  ideal_one_le_ker_counit u hu := by
    have haug := degreeFiltration_le_augmentation ℒ d hneg Nat.zero_lt_one hu
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
    exact (HopfIdeal.mem_augmentation R U).mp (HopfIdeal.mem_toIdeal.mp haug)

/-- For a strictly positive Lie grading, the kernel of the counit lies in the first degree
filtration ideal. -/
theorem ker_counitAlgHom_le_degreeFiltration_one (d : Γ →+ ℤ)
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    RingHom.ker (Bialgebra.counitAlgHom R U) ≤
      (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal 1 := by
  intro u hu
  apply augmentation_le_degreeFiltration_one ℒ d hpos
  rw [HopfIdeal.mem_toIdeal, HopfIdeal.mem_augmentation]
  simpa only [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] using hu

/-- The Lie subalgebra of completed primitive elements inside
`(degreeFiltration ℒ d hneg).completion`, equipped with the associative commutator bracket. -/
noncomputable def completedPrimitives (d : Γ →+ ℤ) (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    LieSubalgebra R (degreeFiltration ℒ d hneg).completion where
  carrier := {x | (degreeFiltration ℒ d hneg).IsCompletedPrimitive R x}
  zero_mem' := AlgFiltration.IsCompletedPrimitive.zero
  add_mem' hx hy := hx.add hy
  smul_mem' r _ hx := hx.smul r
  lie_mem' hx hy := hx.commutator hy

/-- Membership in `completedPrimitives ℒ d hneg` unfolds to `IsCompletedPrimitive`. -/
@[simp]
theorem mem_completedPrimitives_iff (d : Γ →+ ℤ) (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : (degreeFiltration ℒ d hneg).completion} :
    x ∈ completedPrimitives ℒ d hneg ↔
      (degreeFiltration ℒ d hneg).IsCompletedPrimitive R x :=
  Iff.rfl

section PositiveGrading

variable (d : PositiveDegrees Γ) [IsPositiveGrading d ℒ] (hneg : ∀ n, d.degree n < 0 → ℒ n = ⊥)

/-- For a positive grading with respect to `d : PositiveDegrees Γ`, the kernel of the counit lies
in `(degreeFiltration ℒ d.degree hneg).ideal 1`. -/
theorem ker_counitAlgHom_le_positiveDegreeFiltration_one :
    RingHom.ker (Bialgebra.counitAlgHom R U) ≤ (degreeFiltration ℒ d.degree hneg).ideal 1 :=
  ker_counitAlgHom_le_degreeFiltration_one ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ)

/-- Canonical Lie generators from `d.degreeIdeal ℒ k` land in
`(degreeFiltration ℒ d.degree hneg).ideal (k + 1)`. -/
theorem ι_mem_degreeFiltration_of_mem_degreeIdeal {k : ℕ} {x : L}
    (hx : x ∈ d.degreeIdeal ℒ k) :
    ι R x ∈ (degreeFiltration ℒ d.degree hneg).ideal (k + 1) := by
  have hx' : x ∈ d.degreeSubmodule ℒ k := by
    rwa [← d.degreeIdeal_toSubmodule ℒ k]
  rw [d.degreeSubmodule_def ℒ] at hx'
  refine Submodule.iSup_induction _
    (motive := fun x => ι R x ∈ (degreeFiltration ℒ d.degree hneg).ideal (k + 1)) hx'
    (fun n y hy => ι_mem_degreeFiltration ℒ d.degree hneg hy (by have := n.property; omega))
    (by simp) (fun y z hy hz => by simpa only [map_add] using Ideal.add_mem _ hy hz)

/-- The canonical Lie homomorphism from the order-`k` Lie truncation `d.truncatedLie ℒ k` to the
order-`k` enveloping algebra quotient `U(L) ⧸ F.ideal (k + 1)`. -/
noncomputable def truncatedLieToU (k : ℕ) :
    d.truncatedLie ℒ k →ₗ⁅R⁆ U ⧸ (degreeFiltration ℒ d.degree hneg).ideal (k + 1) :=
  (d.degreeIdeal ℒ k).liftQ
    ((Ideal.Quotient.mkₐ R ((degreeFiltration ℒ d.degree hneg).ideal (k + 1))).toLieHom.comp
      (ι R))
    fun x hx => by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using
        ι_mem_degreeFiltration_of_mem_degreeIdeal ℒ d hneg hx

/-- `truncatedLieToU` sends the quotient class of `x : L` to the class of `ι R x`. -/
@[simp]
theorem truncatedLieToU_mk (k : ℕ) (x : L) :
    truncatedLieToU ℒ d hneg k (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk ((degreeFiltration ℒ d.degree hneg).ideal (k + 1)) (ι R x) := by
  simp [truncatedLieToU]

/-- `truncatedLieToU` sends `(d.degreeIdeal ℒ k).mkQ x` to the class of `ι R x`. -/
theorem truncatedLieToU_mkQ (k : ℕ) (x : L) :
    truncatedLieToU ℒ d hneg k ((d.degreeIdeal ℒ k).mkQ x) =
      Ideal.Quotient.mk ((degreeFiltration ℒ d.degree hneg).ideal (k + 1)) (ι R x) := by
  simp [LieIdeal.mkQ_apply]

/-- The finite-order maps `truncatedLieToU` commute with the quotient tower transitions. -/
theorem factor_truncatedLieToU {k m : ℕ} (h : k ≤ m) (z : d.truncatedLie ℒ m) :
    Ideal.Quotient.factor
        ((degreeFiltration ℒ d.degree hneg).antitone (Nat.add_le_add_right h 1))
        (truncatedLieToU ℒ d hneg m z) =
      truncatedLieToU ℒ d hneg k (LieIdeal.factor (d.degreeIdeal_antitone ℒ h) z) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ m).surjective_mkQ z
  simp [LieIdeal.mkQ_apply, LieIdeal.factor_apply]

/-- When `ι R : L → U(L)` is injective, each finite-order Lie map `truncatedLieToU` is injective.
-/
theorem truncatedLieToU_injective (hι : Function.Injective (ι R : L → U)) (k : ℕ) :
    Function.Injective (truncatedLieToU ℒ d hneg k) := by
  rw [truncatedLieToU, LieIdeal.liftQ_injective_iff]
  intro x hx
  have hx' : ι R x ∈ (degreeFiltration ℒ d.degree hneg).ideal (k + 1) := by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hx
  have hmem : x ∈ TauCeti.DirectSum.degreeTail ℒ d.degree (k + 1) := by
    rw [← comap_degreeFiltration_ι ℒ d.degree hneg hι (k + 1)]
    exact hx'
  rw [d.mem_degreeIdeal_iff ℒ]
  intro n hn
  exact (TauCeti.DirectSum.mem_degreeTail_iff ℒ d.degree).mp hmem n (by omega)

/-- The completed Lie homomorphism from `d.completedLie ℒ` to the degree completion of `U(L)`,
assembled from the compatible finite-order maps `truncatedLieToU`. -/
noncomputable def completedLieToU :
    d.completedLie ℒ →ₗ⁅R⁆ (degreeFiltration ℒ d.degree hneg).completion :=
  ((degreeFiltration ℒ d.degree hneg).liftₐ
    (fun k => lift R ((truncatedLieToU ℒ d hneg k).comp
      (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k)))
    (by
      intro k m h
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      ext z
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        lift_ι_apply, Ideal.Quotient.factorₐ_apply]
      exact (factor_truncatedLieToU ℒ d hneg h _).trans
        (congrArg (truncatedLieToU ℒ d hneg k)
          (LieIdeal.factor_completionProjection (d.degreeIdeal ℒ)
            (d.degreeIdeal_antitone ℒ) h z)))).toLieHom.comp
    (ι R)

/-- Projecting `completedLieToU z` to order `k` applies `truncatedLieToU k` to the order-`k` Lie
projection of `z`. -/
@[simp]
theorem projection_completedLieToU (k : ℕ) (z : d.completedLie ℒ) :
    (degreeFiltration ℒ d.degree hneg).projection k (completedLieToU ℒ d hneg z) =
      truncatedLieToU ℒ d hneg k
        (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k z) := by
  simp [completedLieToU]

/-- On canonical images from `L`, `completedLieToU` agrees with `ι R` followed by `toCompletion`. -/
@[simp]
theorem completedLieToU_toCompletion (x : L) :
    completedLieToU ℒ d hneg
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x) =
      (degreeFiltration ℒ d.degree hneg).toCompletion (ι R x) := by
  apply (degreeFiltration ℒ d.degree hneg).completion_ext
  intro k
  simp

/-- Every element in the image of `completedLieToU` belongs to the completed primitive Lie
subalgebra. -/
theorem isCompletedPrimitive_completedLieToU (z : d.completedLie ℒ) :
    (degreeFiltration ℒ d.degree hneg).IsCompletedPrimitive R (completedLieToU ℒ d hneg z) := by
  classical
  rw [AlgFiltration.isCompletedPrimitive_iff_includeCompletion]
  apply ((degreeFiltration ℒ d.degree hneg).tensorProduct R
    (degreeFiltration ℒ d.degree hneg)).completion_ext
  intro k
  let s : L := ∑ n ∈ (d.finite_cutoff k).toFinset,
    (d.completionComponent ℒ
      (fun m => (d.degreeIdeal ℒ m).toSubmodule)
      (fun a b h => (LieSubmodule.toSubmodule_le_toSubmodule _ _).mpr (d.degreeIdeal_antitone ℒ h))
      (fun m => d.degreeIdeal_toSubmodule ℒ m) n z : L)
  have hproj : (degreeFiltration ℒ d.degree hneg).projection k (completedLieToU ℒ d hneg z) =
      (degreeFiltration ℒ d.degree hneg).projection k
        ((degreeFiltration ℒ d.degree hneg).toCompletion (ι R s)) := by
    rw [projection_completedLieToU, d.completionProjection_eq_sum_completionComponent ℒ k z,
      truncatedLieToU_mkQ, AlgFiltration.projection_toCompletion]
  have hs_prim : (degreeFiltration ℒ d.degree hneg).IsCompletedPrimitive R
      ((degreeFiltration ℒ d.degree hneg).toCompletion (ι R s)) :=
    (degreeFiltration ℒ d.degree hneg).isCompletedPrimitive_toCompletion (isPrimitiveElem_ι R L s)
  rw [AlgFiltration.isCompletedPrimitive_iff_includeCompletion] at hs_prim
  have hs_k := congrArg
    (((degreeFiltration ℒ d.degree hneg).tensorProduct R
      (degreeFiltration ℒ d.degree hneg)).projection k) hs_prim
  simpa only [AlgFiltration.projection_completedCoproduct, map_add,
    AlgFiltration.projection_includeLeftCompletion,
    AlgFiltration.projection_includeRightCompletion, hproj] using hs_k

/-- Every element in the image of `completedLieToU` lies in the first completion ideal. -/
theorem completedLieToU_mem_completionIdeal_one (z : d.completedLie ℒ) :
    completedLieToU ℒ d hneg z ∈ (degreeFiltration ℒ d.degree hneg).completionIdeal 1 :=
  (isCompletedPrimitive_completedLieToU ℒ d hneg z).mem_completionIdeal_one
    (ker_counitAlgHom_le_positiveDegreeFiltration_one ℒ d hneg)

/-- When `ι R : L → U(L)` is injective, `completedLieToU` embeds `d.completedLie ℒ` into the degree
completion of `U(L)`. -/
theorem completedLieToU_injective (hι : Function.Injective (ι R : L → U)) :
    Function.Injective (completedLieToU ℒ d hneg) := by
  intro z₁ z₂ hz
  apply LieIdeal.completion_ext
  intro k
  apply truncatedLieToU_injective ℒ d hneg hι k
  simpa only [projection_completedLieToU] using
    congrArg ((degreeFiltration ℒ d.degree hneg).projection k) hz

end PositiveGrading

end GradedBialgebra

end TauCeti.UniversalEnvelopingAlgebra
