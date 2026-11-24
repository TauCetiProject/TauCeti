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

For a `Γ`-graded Lie algebra `L` over a commutative ring `R`, comultiplication on `U(L)` carries
`homogeneousSubmodule ℒ n` into the sum of bidegree tensor summands `U_i ⊗ U_j` with `i + j = n`.
Every nonnegative `UniversalEnvelopingAlgebra.degreeFiltration ℒ d hneg` is therefore a bialgebra
filtration (`AlgFiltration.IsBialgFiltration`), equipping its completion with `completedCoproduct`,
`completedCounit`, and the Lie subalgebra `completedPrimitives`. When `[IsPositiveGrading d ℒ]`,
`L → U(L)` induces compatible finite-order Lie maps `truncatedLieToU` and a completed Lie map
`completedLieToU : d.completedLie ℒ →ₗ⁅R⁆ F.completion`, injective whenever `ι R : L → U(L)` is.

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

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 1–3, Ch. II, §6.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

section Support

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝒰" => homogeneousSubmodule ℒ

attribute [local instance 100] LieRing.ofAssociativeRing

private def bidegreePiece (p : Γ × Γ) : Submodule R (U ⊗[R] U) :=
  Submodule.map₂ (TensorProduct.mk R U U) (𝒰 p.1) (𝒰 p.2)

private def comulHomogeneousSpan (n : Γ) : Submodule R (U ⊗[R] U) :=
  ⨆ p : {p : Γ × Γ // p.1 + p.2 = n}, bidegreePiece ℒ p.val

private theorem comulHomogeneousSpan_le_comap_mulLeft {m n : Γ} {x : L} (hx : x ∈ ℒ m) :
    comulHomogeneousSpan ℒ n ≤ (comulHomogeneousSpan ℒ (m + n)).comap
      (LinearMap.mulLeft R (ι R x ⊗ₜ[R] (1 : U) + (1 : U) ⊗ₜ[R] ι R x)) := by
  refine iSup_le fun p => ?_
  have hx' := ι_mem_homogeneousSubmodule ℒ hx
  have hL : bidegreePiece ℒ p.val ≤ (bidegreePiece ℒ (m + p.val.1, p.val.2)).comap
      (LinearMap.mulLeft R (ι R x ⊗ₜ[R] (1 : U))) := Submodule.map₂_le.mpr fun _ hu _ hv => by
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, TensorProduct.mk_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact Submodule.apply_mem_map₂ _ (SetLike.mul_mem_graded hx' hu) hv
  have hR : bidegreePiece ℒ p.val ≤ (bidegreePiece ℒ (p.val.1, m + p.val.2)).comap
      (LinearMap.mulLeft R ((1 : U) ⊗ₜ[R] ι R x)) := Submodule.map₂_le.mpr fun _ hu _ hv => by
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, TensorProduct.mk_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact Submodule.apply_mem_map₂ _ hu (SetLike.mul_mem_graded hx' hv)
  intro t ht
  simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, add_mul]
  exact add_mem
    (le_iSup (fun q : {q : Γ × Γ // q.1 + q.2 = m + n} => bidegreePiece ℒ q.val)
      ⟨(m + p.val.1, p.val.2), by rw [add_assoc, p.property]⟩ (hL ht))
    (le_iSup (fun q : {q : Γ × Γ // q.1 + q.2 = m + n} => bidegreePiece ℒ q.val)
      ⟨(p.val.1, m + p.val.2), by rw [add_left_comm, p.property]⟩ (hR ht))

private theorem comul_prod_mem_comulHomogeneousSpan (l : List (Σ i, ℒ i)) :
    Coalgebra.comul (R := R) (l.map fun x => ι R (x.2 : L)).prod ∈
      comulHomogeneousSpan ℒ (l.map Sigma.fst).sum := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, Bialgebra.comul_one]
    exact le_iSup (fun q : {q : Γ × Γ // q.1 + q.2 = 0} => bidegreePiece ℒ q.val)
      ⟨(0, 0), add_zero 0⟩
      (Submodule.apply_mem_map₂ _ (SetLike.one_mem_graded 𝒰) (SetLike.one_mem_graded 𝒰))
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Bialgebra.comul_mul, comul_ι]
    exact comulHomogeneousSpan_le_comap_mulLeft ℒ a.2.property ih

private theorem comul_mem_comulHomogeneousSpan {n : Γ} {u : U} (hu : u ∈ 𝒰 n) :
    Coalgebra.comul (R := R) u ∈ comulHomogeneousSpan ℒ n :=
  ((homogeneousSubmodule_le_iff ℒ n
    ((comulHomogeneousSpan ℒ n).comap (Coalgebra.comul (R := R)))).mpr
    fun l hl => hl ▸ comul_prod_mem_comulHomogeneousSpan ℒ l) hu

end Support

section GradedBialgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) [DecidableEq Γ] [GradedLieAlgebra ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝒰" => homogeneousSubmodule ℒ

attribute [local instance 100] LieRing.ofAssociativeRing

/-- On an enveloping element of homogeneous degree `n`, every bidegree projection of `Δ(u)` with
`i + j ≠ n` vanishes. -/
theorem map_proj_comul_eq_zero_of_mem_ne {n : Γ} {u : U} (hu : u ∈ 𝒰 n) {i j : Γ}
    (hij : i + j ≠ n) :
    TensorProduct.map (_root_.GradedAlgebra.proj 𝒰 i) (_root_.GradedAlgebra.proj 𝒰 j)
      (Coalgebra.comul (R := R) u) = 0 := by
  have hker : comulHomogeneousSpan ℒ n ≤ LinearMap.ker
      (TensorProduct.map (_root_.GradedAlgebra.proj 𝒰 i) (_root_.GradedAlgebra.proj 𝒰 j)) :=
    iSup_le fun p _ ht => LinearMap.mem_ker.mpr <| by
      rw [TauCeti.GradedAlgebra.proj_eq_homogeneousComponent,
        TauCeti.GradedAlgebra.proj_eq_homogeneousComponent]
      exact TauCeti.map_homogeneousComponent_eq_zero_of_mem_ne 𝒰 𝒰 ht
        fun hp => hij (by simpa only [hp] using p.property)
  exact LinearMap.mem_ker.mp (hker (comul_mem_comulHomogeneousSpan ℒ hu))

/-- The `(i, j)`-bidegree projection of `Δ(u)` depends only on the `(i + j)`-homogeneous component
of `u`. -/
theorem map_proj_comul (u : U) (i j : Γ) :
    TensorProduct.map (_root_.GradedAlgebra.proj 𝒰 i) (_root_.GradedAlgebra.proj 𝒰 j)
      (Coalgebra.comul (R := R) u) =
    TensorProduct.map (_root_.GradedAlgebra.proj 𝒰 i) (_root_.GradedAlgebra.proj 𝒰 j)
      (Coalgebra.comul (R := R) (DirectSum.decompose 𝒰 u (i + j) : U)) := by
  induction u using _root_.DirectSum.Decomposition.inductionOn 𝒰 with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | @homogeneous m x =>
    by_cases hm : m = i + j
    · subst hm; rw [_root_.DirectSum.decompose_of_mem_same 𝒰 x.property]
    · rw [map_proj_comul_eq_zero_of_mem_ne ℒ x.property (Ne.symm hm),
        _root_.DirectSum.decompose_of_mem_ne 𝒰 x.property hm]; simp

/-- Comultiplication preserves nonnegative degree filtrations on a graded enveloping algebra. -/
theorem degreeFiltration_ideal_le_comap_comul (d : Γ →+ ℤ) (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    (degreeFiltration ℒ d hneg).ideal k ≤ (((degreeFiltration ℒ d hneg).tensorProduct R
      (degreeFiltration ℒ d hneg)).ideal k).comap (Bialgebra.comulAlgHom R U) := fun u hu => by
  rw [Ideal.mem_comap, Bialgebra.comulAlgHom_apply,
    degreeFiltration_eq_gradedAlgebra_degreeFiltration ℒ d hneg,
    TauCeti.GradedAlgebra.mem_tensorProduct_degreeFiltration_ideal_iff]
  intro i j hij
  rw [map_proj_comul, (mem_degreeFiltration_ideal_iff ℒ d hneg).mp hu (i + j)
    (by simpa only [map_add] using hij)]; simp

/-- Every nonnegative degree filtration on a graded enveloping algebra is a bialgebra filtration. -/
instance degreeFiltration_isBialgFiltration (d : Γ →+ ℤ) (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    (degreeFiltration ℒ d hneg).IsBialgFiltration R where
  ideal_le_comap_comul := degreeFiltration_ideal_le_comap_comul ℒ d hneg
  ideal_one_le_ker_counit _ hu := (HopfIdeal.mem_augmentation R U).mp
    (HopfIdeal.mem_toIdeal.mp (degreeFiltration_le_augmentation ℒ d hneg Nat.zero_lt_one hu))

/-- The Lie subalgebra of completed primitive elements inside
`(degreeFiltration ℒ d hneg).completion`, equipped with the associative commutator bracket. -/
noncomputable def completedPrimitives (d : Γ →+ ℤ) (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    LieSubalgebra R (degreeFiltration ℒ d hneg).completion where
  __ := (degreeFiltration ℒ d hneg).completedPrimitiveSubmodule R
  lie_mem' hx hy := (AlgFiltration.mem_completedPrimitiveSubmodule_iff _ _).mpr <|
    ((AlgFiltration.mem_completedPrimitiveSubmodule_iff _ _).mp hx).commutator
      ((AlgFiltration.mem_completedPrimitiveSubmodule_iff _ _).mp hy)

/-- Membership in `completedPrimitives ℒ d hneg` unfolds to `IsCompletedPrimitive`. -/
@[simp] theorem mem_completedPrimitives_iff (d : Γ →+ ℤ) (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : (degreeFiltration ℒ d hneg).completion} :
    x ∈ completedPrimitives ℒ d hneg ↔ (degreeFiltration ℒ d hneg).IsCompletedPrimitive R x :=
  AlgFiltration.mem_completedPrimitiveSubmodule_iff _ _

section PositiveGrading

variable (d : PositiveDegrees Γ) [IsPositiveGrading d ℒ]

local notation "F" => degreeFiltration ℒ (PositiveDegrees.degree d)
  (fun n hn => PositiveDegrees.eq_bot_of_degree_nonpos d ℒ n (le_of_lt hn))

/-- For a positive grading with respect to `d`, `ker ε` lies in `(degreeFiltration ...).ideal 1`. -/
theorem ker_counitAlgHom_le_degreeFiltration_one_of_isPositiveGrading :
    RingHom.ker (Bialgebra.counitAlgHom R U) ≤ (F).ideal 1 :=
  ker_counitAlgHom_le_degreeFiltration_one ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ)

/-- Canonical Lie generators from `d.degreeIdeal ℒ k` land in `(F).ideal (k + 1)`. -/
theorem ι_mem_degreeFiltration_of_mem_degreeIdeal {k : ℕ} {x : L} (hx : x ∈ d.degreeIdeal ℒ k) :
    ι R x ∈ (F).ideal (k + 1) := by
  have hx' : x ∈ d.degreeSubmodule ℒ k := by rwa [← d.degreeIdeal_toSubmodule ℒ k]
  rw [d.degreeSubmodule_def ℒ] at hx'
  exact Submodule.iSup_induction _ (motive := fun x => ι R x ∈ (F).ideal (k + 1)) hx'
    (fun n _ hy => ι_mem_degreeFiltration ℒ d.degree _ hy (by have := n.property; omega))
    (by simp) (fun _ _ hy hz => by simpa only [map_add] using Ideal.add_mem _ hy hz)

/-- The canonical Lie homomorphism from `d.truncatedLie ℒ k` to `U(L) ⧸ (F).ideal (k + 1)`. -/
noncomputable def truncatedLieToU (k : ℕ) : d.truncatedLie ℒ k →ₗ⁅R⁆ U ⧸ (F).ideal (k + 1) :=
  (d.degreeIdeal ℒ k).liftQ ((Ideal.Quotient.mkₐ R ((F).ideal (k + 1))).toLieHom.comp (ι R))
    fun _ hx => by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using ι_mem_degreeFiltration_of_mem_degreeIdeal ℒ d hx

/-- `truncatedLieToU` sends the quotient class of `x : L` to the class of `ι R x`. -/
@[simp] theorem truncatedLieToU_mk (k : ℕ) (x : L) :
    truncatedLieToU ℒ d k (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk ((F).ideal (k + 1)) (ι R x) := by simp [truncatedLieToU]

/-- `truncatedLieToU` sends `(d.degreeIdeal ℒ k).mkQ x` to the class of `ι R x`. -/
theorem truncatedLieToU_mkQ (k : ℕ) (x : L) :
    truncatedLieToU ℒ d k ((d.degreeIdeal ℒ k).mkQ x) =
      Ideal.Quotient.mk ((F).ideal (k + 1)) (ι R x) := by simp [LieIdeal.mkQ_apply]

/-- The finite-order maps `truncatedLieToU` commute with the quotient tower transitions. -/
theorem factor_truncatedLieToU {k m : ℕ} (h : k ≤ m) (z : d.truncatedLie ℒ m) :
    Ideal.Quotient.factor ((F).antitone (Nat.add_le_add_right h 1)) (truncatedLieToU ℒ d m z) =
      truncatedLieToU ℒ d k (LieIdeal.factor (d.degreeIdeal_antitone ℒ h) z) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ m).surjective_mkQ z
  simp [LieIdeal.mkQ_apply, LieIdeal.factor_apply]

/-- When `ι R : L → U(L)` is injective, each `truncatedLieToU` is injective. -/
theorem truncatedLieToU_injective (hι : Function.Injective (ι R : L → U)) (k : ℕ) :
    Function.Injective (truncatedLieToU ℒ d k) := by
  rw [truncatedLieToU, LieIdeal.liftQ_injective_iff]
  intro x hx
  have hmem : x ∈ TauCeti.DirectSum.degreeTail ℒ d.degree (k + 1) := by
    rw [← comap_degreeFiltration_ι ℒ d.degree
      (fun n hn => d.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn)) hι (k + 1)]
    simpa only [LieHom.mem_ker, LieHom.comp_apply, AlgHom.toLieHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_comap, Submodule.restrictScalars_mem,
      LieHom.coe_toLinearMap] using hx
  exact (d.mem_degreeIdeal_iff ℒ).mpr fun n hn =>
    (TauCeti.DirectSum.mem_degreeTail_iff ℒ d.degree).mp hmem n (by omega)

/-- The completed Lie homomorphism from `d.completedLie ℒ` to the degree completion of `U(L)`,
assembled from `truncatedLieToU`. -/
noncomputable def completedLieToU : d.completedLie ℒ →ₗ⁅R⁆ (F).completion :=
  ((F).liftₐ
    (fun k => lift R ((truncatedLieToU ℒ d k).comp
      (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k)))
    (by
      intro k m h; apply _root_.UniversalEnvelopingAlgebra.hom_ext; ext z
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        lift_ι_apply, Ideal.Quotient.factorₐ_apply]
      exact (factor_truncatedLieToU ℒ d h _).trans (congrArg (truncatedLieToU ℒ d k)
        (LieIdeal.factor_completionProjection (d.degreeIdeal ℒ)
          (d.degreeIdeal_antitone ℒ) h z)))).toLieHom.comp (ι R)

/-- Projecting `completedLieToU z` to order `k` applies `truncatedLieToU k` to the order-`k` Lie
projection of `z`. -/
@[simp] theorem projection_completedLieToU (k : ℕ) (z : d.completedLie ℒ) :
    (F).projection k (completedLieToU ℒ d z) =
      truncatedLieToU ℒ d k
        (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k z) := by
  simp [completedLieToU]

/-- On canonical images from `L`, `completedLieToU` agrees with `ι R` followed by `toCompletion`. -/
@[simp] theorem completedLieToU_toCompletion (x : L) :
    completedLieToU ℒ d
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x) =
      (F).toCompletion (ι R x) := (F).completion_ext fun _ => by simp

/-- Every element in the image of `completedLieToU` is completed primitive. -/
@[simp] theorem isCompletedPrimitive_completedLieToU (z : d.completedLie ℒ) :
    (F).IsCompletedPrimitive R (completedLieToU ℒ d z) := by
  rw [AlgFiltration.isCompletedPrimitive_iff_includeCompletion]
  refine ((F).tensorProduct R (F)).completion_ext fun k => ?_
  obtain ⟨s, hs⟩ := (d.degreeIdeal ℒ k).surjective_mkQ
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k z)
  have hproj : (F).projection k (completedLieToU ℒ d z) =
      (F).projection k ((F).toCompletion (ι R s)) := by
    rw [projection_completedLieToU, ← hs, truncatedLieToU_mkQ, (F).projection_toCompletion]
  have hs_prim := congrArg (((F).tensorProduct R (F)).projection k) <|
    ((F).isCompletedPrimitive_iff_includeCompletion R).mp <|
      (F).isCompletedPrimitive_toCompletion (isPrimitiveElem_ι R L s)
  simpa only [AlgFiltration.projection_completedCoproduct, map_add,
    AlgFiltration.projection_includeLeftCompletion,
    AlgFiltration.projection_includeRightCompletion, hproj] using hs_prim

/-- Every element in the image of `completedLieToU` lies in `(F).completionIdeal 1`. -/
theorem completedLieToU_mem_completionIdeal_one (z : d.completedLie ℒ) :
    completedLieToU ℒ d z ∈ (F).completionIdeal 1 :=
  (isCompletedPrimitive_completedLieToU ℒ d z).mem_completionIdeal_one
    (ker_counitAlgHom_le_degreeFiltration_one_of_isPositiveGrading ℒ d)

/-- When `ι R : L → U(L)` is injective, `completedLieToU` is injective. -/
theorem completedLieToU_injective (hι : Function.Injective (ι R : L → U)) :
    Function.Injective (completedLieToU ℒ d) := fun _ _ hz =>
  LieIdeal.completion_ext (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) fun k =>
    truncatedLieToU_injective ℒ d hι k <| by
      simpa only [projection_completedLieToU] using congrArg ((F).projection k) hz

end PositiveGrading

end GradedBialgebra

end TauCeti.UniversalEnvelopingAlgebra
