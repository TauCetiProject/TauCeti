/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Intertwining
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Concrete examples and negative controls for approximate intertwining

This file exercises the approximate unitary equivalence API and Elliott's approximate intertwining
theorems on explicit finite-dimensional and general separable C⋆-algebras:

1. **One-sided approximate inverses fail (`ℂ` vs `ℂ × ℂ`):** for the diagonal embedding
   `diagHom : ℂ →⋆ₙₐ[ℂ] ℂ × ℂ` and first projection `fstHom : ℂ × ℂ →⋆ₙₐ[ℂ] ℂ`, `fstHom ∘ diagHom`
   is the identity on `ℂ`, yet `diagHom ∘ fstHom` is not approximately unitarily equivalent to
   `id_{ℂ × ℂ}` (`not_approximatelyUnitarilyEquivalent_diagHom_comp_fstHom`), and `ℂ` is not
   `⋆`-isomorphic to `ℂ × ℂ` (`isEmpty_starAlgEquiv_complex_prod`). Replacing `diagHom` by the
   first-factor inclusion `inlHom z = (z, 0)` also shows that a one-sided approximate inverse does
   not force unitality (`approximatelyUnitarilyEquivalent_fstHom_comp_inlHom_and_ne_one`).
2. **Rank-one versus full-rank embeddings into `M₂(ℂ)`:** the two rank-one embeddings
   `upperLeftEmb, lowerRightEmb : ℂ →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ` are unitarily (hence
   approximately unitarily) equivalent via the flip unitary, whereas every unitary conjugate of
   `upperLeftEmb 1` lies at C⋆-norm distance `1` from `1` (`norm_conj_upperLeftEmb_one_sub_one`),
   separating `upperLeftEmb` from the unital scalar embedding `scalarEmb`.
3. **Intertwining by a summably Cauchy sequence of unitaries:** if `u : ℕ → unitary A` in a
   separable unital C⋆-algebra satisfies `Summable fun n ↦ ‖(u (n + 1) : A) - (u n : A)‖`, then `u`
   converges to some `u₀ : unitary A`, the inner automorphisms `φ n = Ad(u n)` and
   `ψ n = Ad(star (u n))` satisfy the stationary approximate-intertwining hypotheses with errors
   `0` and `2 * ‖u (n + 1) - u n‖`, and the resulting limit isomorphism equals `Ad(u₀)`
   (`approx_intertwining_conjStarAlgAut`).
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace TauCeti.ElliottIntertwiningExample

/-! ### 1. One-sided approximate inverses (`ℂ` and `ℂ × ℂ`) -/

/-- The unital diagonal `⋆`-homomorphism `z ↦ (z, z)` from `ℂ` into `ℂ × ℂ`. -/
def diagHom : ℂ →⋆ₙₐ[ℂ] ℂ × ℂ where
  toFun z := (z, z)
  map_smul' r z := by simp
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

/-- The first-coordinate projection `(z, w) ↦ z` as a `⋆`-homomorphism `ℂ × ℂ →⋆ₙₐ[ℂ] ℂ`. -/
def fstHom : ℂ × ℂ →⋆ₙₐ[ℂ] ℂ where
  toFun p := p.1
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

/-- The nonunital first-factor inclusion `z ↦ (z, 0)` from `ℂ` into `ℂ × ℂ`. -/
def inlHom : ℂ →⋆ₙₐ[ℂ] ℂ × ℂ where
  toFun z := (z, 0)
  map_smul' r z := by simp
  map_zero' := rfl
  map_add' z w := by simp
  map_mul' z w := by simp
  map_star' z := by simp [Prod.star_def]

@[simp]
theorem fstHom_comp_diagHom : fstHom.comp diagHom = .id ℂ ℂ := by
  ext z
  rfl

/-- `fstHom ∘ diagHom` is approximately unitarily equivalent to `id_ℂ`. -/
theorem approximatelyUnitarilyEquivalent_fstHom_comp_diagHom :
    ApproximatelyUnitarilyEquivalent (fstHom.comp diagHom) (.id ℂ ℂ) := by
  simp

/-- `diagHom ∘ fstHom` is not approximately unitarily equivalent to `id_{ℂ × ℂ}`: every unitary of
the commutative C⋆-algebra `ℂ × ℂ` acts trivially by conjugation, leaving `(1, 1)` at norm distance
`1` from `(1, 0)`. -/
theorem not_approximatelyUnitarilyEquivalent_diagHom_comp_fstHom :
    ¬ ApproximatelyUnitarilyEquivalent (diagHom.comp fstHom) (.id ℂ (ℂ × ℂ)) := by
  intro h
  obtain ⟨u, hu⟩ := (approximatelyUnitarilyEquivalent_def _ _).mp h {(1, 0)} (1 / 2) (by positivity)
  have h1 := hu (1, 0) (Finset.mem_singleton_self _)
  have hcomm : (u : ℂ × ℂ) * (diagHom.comp fstHom) (1, 0) * star (u : ℂ × ℂ) = (1, 1) := by
    calc
      (u : ℂ × ℂ) * (diagHom.comp fstHom) (1, 0) * star (u : ℂ × ℂ)
        = (u : ℂ × ℂ) * 1 * star (u : ℂ × ℂ) := rfl
      _ = (u : ℂ × ℂ) * star (u : ℂ × ℂ) := by rw [mul_one]
      _ = 1 := Unitary.coe_mul_star_self u
  rw [hcomm, NonUnitalStarAlgHom.coe_id, id_eq] at h1
  have hnorm : ‖((1, 1) - (1, 0) : ℂ × ℂ)‖ = 1 := by
    simp [Prod.norm_def]
  linarith

/-- There is no `⋆`-algebra isomorphism between `ℂ` and `ℂ × ℂ`. -/
theorem isEmpty_starAlgEquiv_complex_prod : IsEmpty (ℂ ≃⋆ₐ[ℂ] ℂ × ℂ) := by
  refine ⟨fun e ↦ ?_⟩
  let z : ℂ := e.symm (1, 0)
  have hidem : z * z = z := by
    have hmul : ((1 : ℂ), (0 : ℂ)) * (1, 0) = (1, 0) := by ext <;> simp
    simpa only [z, ← map_mul] using congrArg e.symm hmul
  have hsub : z * (z - 1) = 0 := by
    rw [mul_sub, mul_one, hidem, sub_self]
  rcases mul_eq_zero.mp hsub with hz | hz
  · have h0 : ((1 : ℂ), (0 : ℂ)) = 0 := by
      calc
        ((1 : ℂ), (0 : ℂ)) = e z := (e.apply_symm_apply _).symm
        _ = 0 := by rw [hz, map_zero]
    exact one_ne_zero (congrArg Prod.fst h0)
  · have h1 : ((1 : ℂ), (0 : ℂ)) = 1 := by
      calc
        ((1 : ℂ), (0 : ℂ)) = e z := (e.apply_symm_apply _).symm
        _ = 1 := by rw [sub_eq_zero.mp hz, map_one]
    exact zero_ne_one (congrArg Prod.snd h1)

/-- One-sided approximate invertibility `fstHom ∘ inlHom ≈ᵤ id_ℂ` does not force `inlHom` to be
unital, showing that both hypotheses in `ApproximatelyUnitarilyEquivalent.map_one_of_comp_id` are
needed. -/
theorem approximatelyUnitarilyEquivalent_fstHom_comp_inlHom_and_ne_one :
    ApproximatelyUnitarilyEquivalent (fstHom.comp inlHom) (.id ℂ ℂ) ∧ inlHom 1 ≠ 1 := by
  have hcomp : fstHom.comp inlHom = .id ℂ ℂ := by
    ext z
    rfl
  refine ⟨hcomp ▸ .refl _, fun h ↦ ?_⟩
  exact zero_ne_one (congrArg Prod.snd h)

/-! ### 2. Rank-one versus full-rank embeddings into `CStarMatrix (Fin 2) (Fin 2) ℂ` -/

/-- `2 × 2` complex matrices equipped with their C⋆-algebra structure. -/
abbrev M₂ := CStarMatrix (Fin 2) (Fin 2) ℂ

/-- Embedding `ℂ →⋆ₙₐ[ℂ] M₂` into the `(0, 0)` corner `z ↦ diag(z, 0)`. -/
def upperLeftEmb : ℂ →⋆ₙₐ[ℂ] M₂ where
  toFun z := CStarMatrix.ofMatrix !![z, 0; 0, 0]
  map_smul' r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CStarMatrix.mul_apply, Fin.sum_univ_two]
  map_star' z := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CStarMatrix.star_apply]

/-- Embedding `ℂ →⋆ₙₐ[ℂ] M₂` into the `(1, 1)` corner `z ↦ diag(0, z)`. -/
def lowerRightEmb : ℂ →⋆ₙₐ[ℂ] M₂ where
  toFun z := CStarMatrix.ofMatrix !![0, 0; 0, z]
  map_smul' r z := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CStarMatrix.mul_apply, Fin.sum_univ_two]
  map_star' z := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CStarMatrix.star_apply]

/-- Unital scalar embedding `z ↦ z • 1` from `ℂ` into `M₂`. -/
def scalarEmb : ℂ →⋆ₙₐ[ℂ] M₂ where
  toFun z := z • 1
  map_smul' r z := mul_smul r z 1
  map_zero' := zero_smul ℂ 1
  map_add' z w := add_smul z w 1
  map_mul' z w := by rw [mul_smul, smul_mul_assoc, one_mul]
  map_star' z := by simp [star_smul]

/-- The permutation matrix `[[0, 1], [1, 0]]` as a unitary element of `M₂`. -/
def flipUnitary : unitary M₂ :=
  ⟨CStarMatrix.ofMatrix !![0, 1; 1, 0], by
    rw [Unitary.mem_iff]
    constructor <;> · ext i j; fin_cases i <;> fin_cases j <;>
      simp [CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]⟩

/-- The two rank-one corner embeddings `ℂ →⋆ₙₐ[ℂ] M₂` are unitarily (hence approximately unitarily)
equivalent via `flipUnitary`. -/
theorem approximatelyUnitarilyEquivalent_upperLeftEmb_lowerRightEmb :
    ApproximatelyUnitarilyEquivalent upperLeftEmb lowerRightEmb := by
  refine .of_unitary flipUnitary fun z ↦ ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flipUnitary, upperLeftEmb, lowerRightEmb, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fin.sum_univ_two]

/-- Every unitary conjugate of `upperLeftEmb 1` lies at C⋆-norm distance `1` from `1 : M₂`. -/
theorem norm_conj_upperLeftEmb_one_sub_one (u : unitary M₂) :
    ‖(u : M₂) * upperLeftEmb 1 * star (u : M₂) - 1‖ = 1 := by
  let e := Unitary.conjStarAlgAut ℂ M₂ u
  have hproj : IsStarProjection (e (upperLeftEmb 1)) :=
    ((IsStarProjection.one ℂ).map upperLeftEmb).map e
  have hne : e (upperLeftEmb 1) ≠ 1 := by
    intro h
    have h1 : upperLeftEmb 1 = 1 := e.injective (h.trans (map_one e).symm)
    have hentry := congrArg (fun M : M₂ ↦ M 1 1) h1
    simp [upperLeftEmb] at hentry
  simpa only [e, Unitary.conjStarAlgAut_apply] using hproj.norm_sub_one_eq_one_of_ne_one hne

/-- The rank-one corner embedding `upperLeftEmb` is not approximately unitarily equivalent to the
unital scalar embedding `scalarEmb`. -/
theorem not_approximatelyUnitarilyEquivalent_upperLeftEmb_scalarEmb :
    ¬ ApproximatelyUnitarilyEquivalent upperLeftEmb scalarEmb := by
  intro h
  have h1 : upperLeftEmb 1 = 1 := h.map_one_eq_one_iff.mpr (one_smul ℂ 1)
  have hentry := congrArg (fun M : M₂ ↦ M 1 1) h1
  simp [upperLeftEmb] at hentry

/-- Exercising `elliott_intertwining` on `M₂`: the involutive inner automorphism by `flipUnitary`
and the identity map satisfy the two-sided approximate unitary equivalence hypotheses with the
identity map, yielding a `⋆`-automorphism approximately unitarily equivalent to conjugation by
`flipUnitary`. -/
theorem exists_starAlgEquiv_flipUnitary :
    ∃ θ : M₂ ≃⋆ₐ[ℂ] M₂,
      ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom
        (Unitary.conjStarAlgAut ℂ M₂ flipUnitary).toNonUnitalStarAlgHom := by
  let φ : M₂ →⋆ₙₐ[ℂ] M₂ := (Unitary.conjStarAlgAut ℂ M₂ flipUnitary).toNonUnitalStarAlgHom
  have hφ : ApproximatelyUnitarilyEquivalent φ (.id ℂ M₂) :=
    (ApproximatelyUnitarilyEquivalent.of_unitary flipUnitary fun _ ↦ rfl).symm
  refine elliott_intertwining φ (.id ℂ M₂) ?_ ?_
  · simpa using hφ
  · simpa using hφ

/-! ### 3. Summable unitary-conjugation intertwining (`Ad(u_n)` and `Ad(star (u_n))`) -/

private theorem exists_nested_unitBall_finsets {A : Type*} [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] (u : ℕ → unitary A) :
    ∃ F G : ℕ → Finset A,
      Monotone F ∧ Monotone G ∧
      (∀ n, ∀ a ∈ F n, (Unitary.conjStarAlgAut ℂ A (u n)) a ∈ G n) ∧
      (∀ n, ∀ b ∈ G n, (Unitary.conjStarAlgAut ℂ A (star (u n))) b ∈ F (n + 1)) ∧
      Dense (NonUnitalStarAlgebra.adjoin ℂ (⋃ n, (F n : Set A)) : Set A) ∧
      Dense (NonUnitalStarAlgebra.adjoin ℂ (⋃ n, (G n : Set A)) : Set A) ∧
      (∀ n, ∀ b ∈ G n, ‖b‖ ≤ 1) := by
  classical
  -- Phase 1: rescale a dense sequence into the closed unit ball while keeping its span dense.
  let φ (n : ℕ) : A →⋆ₙₐ[ℂ] A := (Unitary.conjStarAlgAut ℂ A (u n)).toNonUnitalStarAlgHom
  let ψ (n : ℕ) : A →⋆ₙₐ[ℂ] A := (Unitary.conjStarAlgAut ℂ A (star (u n))).toNonUnitalStarAlgHom
  let d0 : ℕ → A := TopologicalSpace.denseSeq A
  let d (n : ℕ) : A := (((1 + ‖d0 n‖ : ℝ) : ℂ)⁻¹) • d0 n
  have hd_norm (n : ℕ) : ‖d n‖ ≤ 1 := by
    have hpos : 0 < 1 + ‖d0 n‖ := by positivity
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpos.le,
      inv_mul_le_iff₀ hpos]
    linarith
  -- Phase 2: build nested finite sets `F n` and `G n` closed under `φ n` and `ψ n`.
  let FG : ℕ → Finset A × Finset A :=
    Nat.rec
      (let F₀ : Finset A := {d 0}
       (F₀, F₀.image (φ 0) ∪ {d 0}))
      (fun n p ↦
       let F' : Finset A := p.1 ∪ p.2.image (ψ n) ∪ {d (n + 1)}
       (F', p.2 ∪ F'.image (φ (n + 1)) ∪ {d (n + 1)}))
  let F (n : ℕ) : Finset A := (FG n).1
  let G (n : ℕ) : Finset A := (FG n).2
  have hF_mono : Monotone F := monotone_nat_of_le_succ fun n ↦
    Finset.subset_union_left.trans Finset.subset_union_left
  have hG_mono : Monotone G := monotone_nat_of_le_succ fun n ↦
    Finset.subset_union_left.trans Finset.subset_union_left
  have hφG (n : ℕ) (a : A) (ha : a ∈ F n) : φ n a ∈ G n := by
    cases n with
    | zero => exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
    | succ n =>
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))
  have hψF (n : ℕ) (b : A) (hb : b ∈ G n) : ψ n b ∈ F (n + 1) :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb))
  have hdF (n : ℕ) : d n ∈ F n := by
    cases n with
    | zero => exact Finset.mem_singleton_self _
    | succ n => exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hdG (n : ℕ) : d n ∈ G n := by
    cases n with
    | zero => exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    | succ n => exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  -- Phase 3: verify density of the generated `⋆`-subalgebras and the unit-ball norm bound.
  have hdense_of_mem {S : ℕ → Finset A} (hdS : ∀ n, d n ∈ S n) :
      Dense (NonUnitalStarAlgebra.adjoin ℂ (⋃ n, (S n : Set A)) : Set A) := by
    refine (TopologicalSpace.denseRange_denseSeq A).mono ?_
    rintro _ ⟨n, rfl⟩
    have hc : ((1 + ‖d0 n‖ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (0 : ℝ) < 1 + ‖d0 n‖).ne'
    have hmem : d n ∈ NonUnitalStarAlgebra.adjoin ℂ (⋃ k, (S k : Set A)) :=
      NonUnitalStarAlgebra.subset_adjoin ℂ _ (Set.mem_iUnion.mpr ⟨n, hdS n⟩)
    have hsmul : ((1 + ‖d0 n‖ : ℝ) : ℂ) • d n ∈
        NonUnitalStarAlgebra.adjoin ℂ (⋃ k, (S k : Set A)) :=
      Submodule.smul_mem
        (NonUnitalStarAlgebra.adjoin ℂ (⋃ k, (S k : Set A))).toSubmodule
        ((1 + ‖d0 n‖ : ℝ) : ℂ) hmem
    simpa only [d, d0, smul_smul, mul_inv_cancel₀ hc, one_smul, SetLike.mem_coe] using hsmul
  have hFG_norm (n : ℕ) : (∀ a ∈ F n, ‖a‖ ≤ 1) ∧ (∀ b ∈ G n, ‖b‖ ≤ 1) := by
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro a ha
        rw [Finset.mem_singleton.mp ha]
        exact hd_norm 0
      · intro b hb
        rcases Finset.mem_union.mp hb with hb | hb
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
          rw [Finset.mem_singleton.mp ha]
          simpa [φ] using (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ A (u 0)) (d 0)).trans_le
            (hd_norm 0)
        · rw [Finset.mem_singleton.mp hb]
          exact hd_norm 0
    | succ n ih =>
      have hF' : ∀ a ∈ F (n + 1), ‖a‖ ≤ 1 := by
        intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · rcases Finset.mem_union.mp ha with ha | ha
          · exact ih.1 a ha
          · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
            simpa [ψ] using
              (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ A (star (u n))) b).trans_le
                (ih.2 b hb)
        · rw [Finset.mem_singleton.mp ha]
          exact hd_norm (n + 1)
      refine ⟨hF', fun b hb ↦ ?_⟩
      rcases Finset.mem_union.mp hb with hb | hb
      · rcases Finset.mem_union.mp hb with hb | hb
        · exact ih.2 b hb
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
          simpa [φ] using
            (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ A (u (n + 1))) a).trans_le (hF' a ha)
      · rw [Finset.mem_singleton.mp hb]
        exact hd_norm (n + 1)
  exact ⟨F, G, hF_mono, hG_mono, hφG, hψF, hdense_of_mem hdF, hdense_of_mem hdG,
    fun n ↦ (hFG_norm n).2⟩

/-- When `u : ℕ → unitary A` in a separable unital C⋆-algebra has summable consecutive differences
`Summable fun n ↦ ‖(u (n + 1) : A) - (u n : A)‖`, `u` converges to a unitary `u₀ : unitary A`, the
inner automorphisms `φ n = Ad(u n)` and `ψ n = Ad(star (u n))` satisfy the hypotheses of
`exists_starAlgEquiv_of_approx_intertwining` with errors `δ n = 0` and
`ε n = 2 * ‖(u (n + 1) : A) - (u n : A)‖` on nested finite subsets of the closed unit ball, and
their point-norm limit isomorphism is `Unitary.conjStarAlgAut ℂ A u₀`. -/
theorem approx_intertwining_conjStarAlgAut {A : Type*} [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] {u : ℕ → unitary A}
    (hu : Summable fun n ↦ ‖(u (n + 1) : A) - (u n : A)‖) :
    ∃ u₀ : unitary A,
      Tendsto u atTop (𝓝 u₀) ∧
      ∃ F G : ℕ → Finset A,
        Monotone F ∧ Monotone G ∧
        (∀ n, ∀ a ∈ F n, (Unitary.conjStarAlgAut ℂ A (u n)) a ∈ G n) ∧
        (∀ n, ∀ b ∈ G n, (Unitary.conjStarAlgAut ℂ A (star (u n))) b ∈ F (n + 1)) ∧
        Dense (NonUnitalStarAlgebra.adjoin ℂ (⋃ n, (F n : Set A)) : Set A) ∧
        Dense (NonUnitalStarAlgebra.adjoin ℂ (⋃ n, (G n : Set A)) : Set A) ∧
        (∀ n, ∀ a ∈ F n,
          ‖(Unitary.conjStarAlgAut ℂ A (star (u n))) ((Unitary.conjStarAlgAut ℂ A (u n)) a) - a‖ ≤
            0) ∧
        (∀ n, ∀ b ∈ G n,
          ‖(Unitary.conjStarAlgAut ℂ A (u (n + 1)))
              ((Unitary.conjStarAlgAut ℂ A (star (u n))) b) - b‖ ≤
            2 * ‖(u (n + 1) : A) - (u n : A)‖) ∧
        (∃ θ : A ≃⋆ₐ[ℂ] A,
          Tendsto (fun n ↦ (Unitary.conjStarAlgAut ℂ A (u n)).toNonUnitalStarAlgHom) atTop
            (𝓝 θ.toNonUnitalStarAlgHom) ∧
          θ = Unitary.conjStarAlgAut ℂ A u₀) := by
  have hcauchy : CauchySeq fun n ↦ (u n : A) :=
    cauchySeq_of_dist_le_of_summable (fun n ↦ ‖(u (n + 1) : A) - (u n : A)‖)
      (fun n ↦ by rw [dist_comm, dist_eq_norm]) hu
  obtain ⟨x₀, hx₀⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hx₀_mem : x₀ ∈ unitary A :=
    isClosed_unitary.mem_of_tendsto hx₀ (Eventually.of_forall fun n ↦ (u n).2)
  let u₀ : unitary A := ⟨x₀, hx₀_mem⟩
  have hu₀ : Tendsto u atTop (𝓝 u₀) := tendsto_subtype_rng.mpr hx₀
  let φ (n : ℕ) : A →⋆ₙₐ[ℂ] A := (Unitary.conjStarAlgAut ℂ A (u n)).toNonUnitalStarAlgHom
  let ψ (n : ℕ) : A →⋆ₙₐ[ℂ] A := (Unitary.conjStarAlgAut ℂ A (star (u n))).toNonUnitalStarAlgHom
  obtain ⟨F, G, hF_mono, hG_mono, hφG, hψF, hF_dense, hG_dense, hG_norm⟩ :=
    exists_nested_unitBall_finsets u
  have herr_A (n : ℕ) (a : A) (_ : a ∈ F n) : ‖ψ n (φ n a) - a‖ ≤ 0 := by
    have hinv : ψ n (φ n a) = a := by
      simpa [φ, ψ, ← Unitary.conjStarAlgAut_symm] using
        (Unitary.conjStarAlgAut ℂ A (u n)).symm_apply_apply a
    simp [hinv]
  have herr_B (n : ℕ) (b : A) (hb : b ∈ G n) :
      ‖φ (n + 1) (ψ n b) - b‖ ≤ 2 * ‖(u (n + 1) : A) - (u n : A)‖ := by
    calc
      ‖φ (n + 1) (ψ n b) - b‖ ≤ 2 * ‖b‖ * ‖(u (n + 1) : A) - (u n : A)‖ :=
        Unitary.norm_conjStarAlgAut_star_sub_le (u n) (u (n + 1)) b
      _ ≤ 2 * 1 * ‖(u (n + 1) : A) - (u n : A)‖ := by
        gcongr
        exact hG_norm n b hb
      _ = 2 * ‖(u (n + 1) : A) - (u n : A)‖ := by ring
  obtain ⟨θ, hθ_tendsto, -, -, -⟩ := exists_starAlgEquiv_of_approx_intertwining
    φ ψ F G hF_mono hG_mono hφG hψF hF_dense hG_dense
    summable_zero (hu.mul_left 2) herr_A herr_B
  have hφ_u₀ : Tendsto φ atTop (𝓝 (Unitary.conjStarAlgAut ℂ A u₀).toNonUnitalStarAlgHom) :=
    (Unitary.continuous_conjStarAlgAut_toNonUnitalStarAlgHom.tendsto u₀).comp hu₀
  have hθ_eq : θ = Unitary.conjStarAlgAut ℂ A u₀ := by
    have hhom := tendsto_nhds_unique hθ_tendsto hφ_u₀
    ext a
    exact congr($hhom a)
  exact ⟨u₀, hu₀, F, G, hF_mono, hG_mono, hφG, hψF, hF_dense, hG_dense,
    herr_A, herr_B, θ, hθ_tendsto, hθ_eq⟩

end TauCeti.ElliottIntertwiningExample
