/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Algebra.Star.DirectedSystem
public import TauCeti.Analysis.CStarAlgebra.InductiveLimit
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Sequential colimit cocones of C⋆-algebras

Given a sequential inductive system `A₀ →[α₀] A₁ →[α₁] ⋯` of (possibly non-unital) C⋆-algebras
with possibly non-injective connecting maps, a compatible family of `⋆`-homomorphisms
`ι : ∀ n, A n →⋆ₙₐ[ℂ] C` into a C⋆-algebra `C` is a *sequential colimit cocone*
(`IsSeqColimitCocone α ι`) when the union of stage images `⋃ n, Set.range (ι n)` is dense in `C`
and the stage seminorms `k ↦ ‖seqTransHom α _ a‖` converge to `‖ι n a‖` as `k → ∞`.

Because `⋆`-homomorphisms between C⋆-algebras are contractive, any compatible cocone
`ξ : ∀ n, A n →⋆ₙₐ[ℂ] D` into another C⋆-algebra `D` satisfies `‖ξ n a‖ ≤ ‖ι n a‖` on every stage,
so it is well-defined and `1`-Lipschitz on the dense union of stage images and extends uniquely to
a `⋆`-homomorphism `hι.lift ξ hξ : C →⋆ₙₐ[ℂ] D`.

## Main definitions and results

* `TauCeti.antitone_norm_seqTransHom`: contractivity makes `k ↦ ‖seqTransHom α _ a‖` antitone.
* `TauCeti.IsSeqColimitCocone`: predicate characterizing a sequential C⋆-algebra colimit cocone,
  with the `⨅`-seminorm formula `norm_eq_ciInf` / `of_norm_eq_ciInf`, constructors `of_isometry`,
  `const`, `of_nonUnitalStarSubalgebra`, and `of_starSubalgebra`, and extensionality principles
  `hom_ext` and `hom_ext_of_approx`.
* `TauCeti.IsSeqColimitCocone.lift`: universal lift `C →⋆ₙₐ[ℂ] D` of any compatible cocone `ξ`,
  characterized by `lift_apply`, `lift_comp`, and `lift_unique`, and the canonical comparison
  `⋆`-isomorphism `IsSeqColimitCocone.equiv` between two colimit realizations.
* `TauCeti.CStarInductiveLimit.isSeqColimitCocone_of`: `CStarInductiveLimit.of` for the system
  `seqTransHom α` forms a sequential colimit cocone.

## References

* M. Rørdam, *Classification of Nuclear C⋆-Algebras*, Encyclopaedia of Mathematical Sciences 126,
  Springer (2002), §2.3; M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for
  C⋆-Algebras*, LMSST 49, Cambridge University Press (2000), §6.2.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti

variable {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)]
  {C : Type*} [NonUnitalCStarAlgebra C]

/-- For any sequential system of C⋆-algebras, the seminorm `k ↦ ‖seqTransHom α _ a‖` is
antitone because `⋆`-homomorphisms between C⋆-algebras are contractive. -/
theorem antitone_norm_seqTransHom (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (n : ℕ) (a : A n) :
    Antitone (fun k ↦ ‖seqTransHom α (Nat.le_add_right n k) a‖) := by
  intro i j hij
  dsimp only
  rw [← seqTransHom_comp_apply α (Nat.le_add_right n i) (Nat.add_le_add_left hij n) a]
  exact NonUnitalStarAlgHom.norm_apply_le _ _

/-- A compatible cocone `ι : ∀ n, A n →⋆ₙₐ[ℂ] C` from a sequential system of C⋆-algebras
`(A, α)` into `C` is a *sequential colimit cocone* when `(ι (n + 1)).comp (α n) = ι n` for every
`n`, the union `⋃ n, Set.range (ι n)` is dense in `C`, and `‖seqTransHom α _ a‖ → ‖ι n a‖` as
the offset tends to infinity. Connecting maps `α n` need not be injective. -/
structure IsSeqColimitCocone (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1))
    (ι : ∀ n, A n →⋆ₙₐ[ℂ] C) : Prop where
  /-- Compatibility of the cocone maps with the connecting maps. -/
  comp_eq (n : ℕ) : (ι (n + 1)).comp (α n) = ι n
  /-- Density of the algebraic union of stage images inside `C`. -/
  dense_iUnion_range : Dense (⋃ n, Set.range (ι n))
  /-- Asymptotic seminorm formula along the connecting maps. -/
  tendsto_norm (n : ℕ) (a : A n) :
    Tendsto (fun k ↦ ‖seqTransHom α (Nat.le_add_right n k) a‖) atTop (𝓝 ‖ι n a‖)

namespace IsSeqColimitCocone

variable {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {ι : ∀ n, A n →⋆ₙₐ[ℂ] C}

theorem comp_apply (hι : IsSeqColimitCocone α ι) (n : ℕ) (a : A n) :
    ι (n + 1) (α n a) = ι n a :=
  DFunLike.congr_fun (hι.comp_eq n) a

theorem comp_seqTransHom (hι : IsSeqColimitCocone α ι) {m n : ℕ} (h : m ≤ n) :
    (ι n).comp (seqTransHom α h) = ι m :=
  comp_seqTransHom_of_comp_eq hι.comp_eq h

theorem comp_seqTransHom_apply (hι : IsSeqColimitCocone α ι) {m n : ℕ} (h : m ≤ n) (a : A m) :
    ι n (seqTransHom α h a) = ι m a :=
  DFunLike.congr_fun (hι.comp_seqTransHom h) a

/-- In a sequential colimit cocone, the norm in `C` of a stage element is the infimum of its
forward norms along the system. -/
theorem norm_eq_ciInf (hι : IsSeqColimitCocone α ι) (n : ℕ) (a : A n) :
    ‖ι n a‖ = ⨅ k, ‖seqTransHom α (Nat.le_add_right n k) a‖ := by
  refine tendsto_nhds_unique (hι.tendsto_norm n a) (tendsto_atTop_ciInf
    (antitone_norm_seqTransHom α n a) ⟨0, ?_⟩)
  rintro _ ⟨k, rfl⟩
  exact norm_nonneg _

/-- Constructor for `IsSeqColimitCocone` from the `⨅`-characterization of the limit norm. -/
theorem of_norm_eq_ciInf (hcomp : ∀ n, (ι (n + 1)).comp (α n) = ι n)
    (hdense : Dense (⋃ n, Set.range (ι n)))
    (hnorm : ∀ n a, ‖ι n a‖ = ⨅ k, ‖seqTransHom α (Nat.le_add_right n k) a‖) :
    IsSeqColimitCocone α ι where
  comp_eq := hcomp
  dense_iUnion_range := hdense
  tendsto_norm n a := by
    rw [hnorm n a]
    exact tendsto_atTop_ciInf (antitone_norm_seqTransHom α n a)
      ⟨0, by rintro _ ⟨k, rfl⟩; exact norm_nonneg _⟩

/-- Any compatible cocone of isometric `⋆`-homomorphisms whose ranges have dense union is a
sequential colimit cocone. -/
theorem of_isometry (hcomp : ∀ n, (ι (n + 1)).comp (α n) = ι n)
    (hdense : Dense (⋃ n, Set.range (ι n))) (hiso : ∀ n, Isometry (ι n)) :
    IsSeqColimitCocone α ι where
  comp_eq := hcomp
  dense_iUnion_range := hdense
  tendsto_norm n a := by
    have hnorm_eq (m : ℕ) (x : A m) : ‖ι m x‖ = ‖x‖ := by
      simpa only [dist_zero_right, map_zero] using (hiso m).dist_eq x 0
    have hnorm (k : ℕ) : ‖seqTransHom α (Nat.le_add_right n k) a‖ = ‖ι n a‖ := by
      rw [← hnorm_eq (n + k), comp_seqTransHom_apply_of_comp_eq hcomp]
    simp_rw [hnorm]
    exact tendsto_const_nhds

/-- The constant system `C →[id] C →[id] ⋯` with identity cocone maps is a sequential colimit
cocone. -/
theorem const (C : Type*) [NonUnitalCStarAlgebra C] :
    IsSeqColimitCocone (A := fun _ ↦ C) (fun _ ↦ .id ℂ C) (fun _ ↦ .id ℂ C) :=
  of_isometry (fun _ ↦ rfl) (by simp [Set.iUnion_const]) (fun _ ↦ isometry_id)

/-- An increasing sequence of closed non-unital `⋆`-subalgebras with dense union forms a sequential
colimit cocone under subtype inclusions. -/
theorem of_nonUnitalStarSubalgebra {S : ℕ → NonUnitalStarSubalgebra ℂ C}
    [∀ n, IsClosed (S n : Set C)] (hS : Monotone S) (hdense : Dense (⋃ n, (S n : Set C))) :
    IsSeqColimitCocone (fun n ↦ NonUnitalStarSubalgebra.inclusion (hS (Nat.le_succ n)))
      (fun n ↦ NonUnitalStarSubalgebraClass.subtype (S n)) := by
  refine of_isometry (fun _ ↦ rfl) ?_ (fun _ ↦ isometry_subtypeVal)
  have hr (n : ℕ) : Set.range ⇑(NonUnitalStarSubalgebraClass.subtype (S n)) = (S n : Set C) := by
    ext x
    simp
  simp_rw [hr]
  exact hdense

/-- An increasing sequence of closed unital `⋆`-subalgebras of a unital C⋆-algebra `E` with dense
union forms a sequential colimit cocone of unital C⋆-algebras under subtype inclusions. -/
theorem of_starSubalgebra {E : Type*} [CStarAlgebra E] {S : ℕ → StarSubalgebra ℂ E}
    [∀ n, IsClosed (S n : Set E)] (hS : Monotone S) (hdense : Dense (⋃ n, (S n : Set E))) :
    IsSeqColimitCocone
      (fun n ↦ (StarSubalgebra.inclusion (hS (Nat.le_succ n))).toNonUnitalStarAlgHom)
      (fun n ↦ (S n).subtype.toNonUnitalStarAlgHom) := by
  refine of_isometry (fun _ ↦ rfl) ?_ (fun _ ↦ isometry_subtypeVal)
  have hr (n : ℕ) : Set.range ⇑(S n).subtype.toNonUnitalStarAlgHom = (S n : Set E) := by
    ext x
    simp
  simp_rw [hr]
  exact hdense

/-- If stage subsets `F n ⊆ A n` asymptotically approximate every stage element along `α`, then
the union of their stage images `⋃ n, ι n '' F n` is dense in `C`. -/
theorem dense_iUnion_image_of_approx (hι : IsSeqColimitCocone α ι) {F : ∀ n, Set (A n)}
    (happrox : ∀ n (a : A n) (r : ℝ),
      0 < r → ∃ k, ∃ x ∈ F (n + k), ‖seqTransHom α (Nat.le_add_right n k) a - x‖ < r) :
    Dense (⋃ n, ι n '' F n) := by
  refine (hι.dense_iUnion_range.mono ?_).of_closure
  refine Set.iUnion_subset fun n ↦ Set.range_subset_iff.mpr fun a ↦
    Metric.mem_closure_iff.mpr fun r hr ↦ ?_
  obtain ⟨k, x, hxF, hax⟩ := happrox n a r hr
  refine ⟨ι (n + k) x, Set.mem_iUnion.mpr ⟨n + k, x, hxF, rfl⟩, ?_⟩
  rw [dist_eq_norm, ← hι.comp_seqTransHom_apply (Nat.le_add_right n k) a, ← map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans_lt hax

/-- Two `⋆`-homomorphisms out of `C` that agree on stage subsets `F n ⊆ A n` asymptotically
approximating every stage element along `α` are equal. -/
theorem hom_ext_of_approx {D : Type*} [NonUnitalCStarAlgebra D] (hι : IsSeqColimitCocone α ι)
    {F : ∀ n, Set (A n)}
    (happrox : ∀ n (a : A n) (r : ℝ),
      0 < r → ∃ k, ∃ x ∈ F (n + k), ‖seqTransHom α (Nat.le_add_right n k) a - x‖ < r)
    {Φ₁ Φ₂ : C →⋆ₙₐ[ℂ] D} (h : ∀ n ⦃a⦄, a ∈ F n → Φ₁ (ι n a) = Φ₂ (ι n a)) :
    Φ₁ = Φ₂ := by
  have heq : Set.EqOn Φ₁ Φ₂ (closure (⋃ n, ι n '' F n)) := by
    refine Set.EqOn.closure (fun x hx ↦ ?_) (map_continuous Φ₁) (map_continuous Φ₂)
    rcases Set.mem_iUnion.mp hx with ⟨n, a, ha, rfl⟩
    exact h n ha
  ext x
  exact heq (hι.dense_iUnion_image_of_approx happrox x)

/-- Two `⋆`-homomorphisms out of `C` that agree on every stage of a sequential colimit cocone are
equal. -/
theorem hom_ext {D : Type*} [NonUnitalCStarAlgebra D] (hι : IsSeqColimitCocone α ι)
    {Φ₁ Φ₂ : C →⋆ₙₐ[ℂ] D} (h : ∀ n a, Φ₁ (ι n a) = Φ₂ (ι n a)) : Φ₁ = Φ₂ :=
  hι.hom_ext_of_approx (F := fun _ ↦ Set.univ)
    (fun _ a _ hr ↦ ⟨0, a, trivial, by simpa using hr⟩) fun n a _ ↦ h n a

private theorem norm_le_of_comp_eq {D : Type*} [NonUnitalCStarAlgebra D]
    (hι : IsSeqColimitCocone α ι) {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D}
    (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) (n : ℕ) (a : A n) : ‖ξ n a‖ ≤ ‖ι n a‖ :=
  ge_of_tendsto' (hι.tendsto_norm n a) fun k ↦ by
    rw [← comp_seqTransHom_apply_of_comp_eq hξ (Nat.le_add_right n k) a]
    exact NonUnitalStarAlgHom.norm_apply_le _ _

/-- Induced contractive map on the dense subtype `↥(⋃ n, Set.range (ι n))`. -/
private noncomputable def unionFun {D : Type*} [NonUnitalCStarAlgebra D]
    (ι : ∀ n, A n →⋆ₙₐ[ℂ] C) (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D) (u : ↥(⋃ n, Set.range (ι n))) : D := by
  classical
  exact ξ (Set.mem_iUnion.mp u.property).choose (Set.mem_iUnion.mp u.property).choose_spec.choose

private theorem unionFun_apply {D : Type*} [NonUnitalCStarAlgebra D]
    (hι : IsSeqColimitCocone α ι) {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D}
    (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) (n : ℕ) (a : A n)
    (hu : ι n a ∈ ⋃ m, Set.range (ι m)) :
    unionFun ι ξ ⟨ι n a, hu⟩ = ξ n a := by
  classical
  dsimp only [unionFun]
  set m := (Set.mem_iUnion.mp hu).choose
  set b := (Set.mem_iUnion.mp hu).choose_spec.choose
  have hmb : ι m b = ι n a := (Set.mem_iUnion.mp hu).choose_spec.choose_spec
  let N := max m n
  have hN : ι N (seqTransHom α (le_max_left m n) b - seqTransHom α (le_max_right m n) a) = 0 := by
    rw [map_sub, hι.comp_seqTransHom_apply, hι.comp_seqTransHom_apply, hmb, sub_self]
  have h0 : ξ N (seqTransHom α (le_max_left m n) b - seqTransHom α (le_max_right m n) a) = 0 :=
    norm_le_zero_iff.mp <| (hι.norm_le_of_comp_eq hξ N _).trans (by simp [hN])
  rw [map_sub, comp_seqTransHom_apply_of_comp_eq hξ, comp_seqTransHom_apply_of_comp_eq hξ,
    sub_eq_zero] at h0
  exact h0

private theorem lipschitzWith_unionFun {D : Type*} [NonUnitalCStarAlgebra D]
    (hι : IsSeqColimitCocone α ι) {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D}
    (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) :
    LipschitzWith 1 (unionFun ι ξ) := by
  refine LipschitzWith.of_dist_le_mul ?_
  rintro ⟨_, hu₁⟩ ⟨_, hu₂⟩
  rcases Set.mem_iUnion.mp hu₁ with ⟨n₁, a₁, rfl⟩
  rcases Set.mem_iUnion.mp hu₂ with ⟨n₂, a₂, rfl⟩
  rw [NNReal.coe_one, one_mul, dist_eq_norm,
    hι.unionFun_apply hξ n₁ a₁ hu₁, hι.unionFun_apply hξ n₂ a₂ hu₂,
    ← comp_seqTransHom_apply_of_comp_eq hξ (le_max_left n₁ n₂) a₁,
    ← comp_seqTransHom_apply_of_comp_eq hξ (le_max_right n₁ n₂) a₂, ← map_sub]
  refine (hι.norm_le_of_comp_eq hξ (max n₁ n₂) _).trans ?_
  rw [map_sub, hι.comp_seqTransHom_apply, hι.comp_seqTransHom_apply, Subtype.dist_eq, dist_eq_norm]

private noncomputable def extendUnionFun {D : Type*} [NonUnitalCStarAlgebra D]
    (hι : IsSeqColimitCocone α ι) (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D) : C → D :=
  hι.dense_iUnion_range.extend (unionFun ι ξ)

private theorem continuous_extendUnionFun {D : Type*} [NonUnitalCStarAlgebra D]
    (hι : IsSeqColimitCocone α ι) {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D}
    (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) :
    Continuous (hι.extendUnionFun ξ) :=
  (hι.dense_iUnion_range.uniformContinuous_extend
    (hι.lipschitzWith_unionFun hξ).uniformContinuous).continuous

private theorem extendUnionFun_apply {D : Type*} [NonUnitalCStarAlgebra D]
    (hι : IsSeqColimitCocone α ι) {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D}
    (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) (n : ℕ) (a : A n) :
    hι.extendUnionFun ξ (ι n a) = ξ n a := by
  have hu : ι n a ∈ ⋃ m, Set.range (ι m) := Set.mem_iUnion.mpr ⟨n, a, rfl⟩
  exact (hι.dense_iUnion_range.extend_of_ind
    (hι.lipschitzWith_unionFun hξ).uniformContinuous ⟨ι n a, hu⟩).trans
    (hι.unionFun_apply hξ n a hu)

private theorem extendUnionFun_map₂ {D : Type*} [NonUnitalCStarAlgebra D]
    (hι : IsSeqColimitCocone α ι) {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D}
    (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n)
    (opA : ∀ n, A n → A n → A n) (opC : C → C → C) (opD : D → D → D)
    (hopC : Continuous fun p : C × C ↦ opC p.1 p.2)
    (hopD : Continuous fun p : D × D ↦ opD p.1 p.2)
    (hι_op : ∀ n x y, ι n (opA n x y) = opC (ι n x) (ι n y))
    (hξ_op : ∀ n x y, ξ n (opA n x y) = opD (ξ n x) (ξ n y)) (x y : C) :
    hι.extendUnionFun ξ (opC x y) = opD (hι.extendUnionFun ξ x) (hι.extendUnionFun ξ y) := by
  let cont := hι.continuous_extendUnionFun hξ
  refine hι.dense_iUnion_range.denseRange_subtypeVal.induction_on₂
    (isClosed_eq (cont.comp hopC) (hopD.comp (cont.prodMap cont))) ?_ x y
  rintro ⟨_, ⟨_, ⟨n₁, rfl⟩, a₁, rfl⟩⟩ ⟨_, ⟨_, ⟨n₂, rfl⟩, a₂, rfl⟩⟩
  dsimp only
  rw [← hι.comp_seqTransHom_apply (le_max_left n₁ n₂) a₁,
    ← hι.comp_seqTransHom_apply (le_max_right n₁ n₂) a₂, ← hι_op,
    hι.extendUnionFun_apply hξ, hι.extendUnionFun_apply hξ,
    hι.extendUnionFun_apply hξ, hξ_op]

/-- Universal property of a sequential colimit cocone: any compatible family of stage
`⋆`-homomorphisms `ξ : ∀ n, A n →⋆ₙₐ[ℂ] D` descends to a `⋆`-homomorphism `C →⋆ₙₐ[ℂ] D`. -/
noncomputable def lift {D : Type*} [NonUnitalCStarAlgebra D] (hι : IsSeqColimitCocone α ι)
    (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) : C →⋆ₙₐ[ℂ] D where
  toFun := hι.extendUnionFun ξ
  map_zero' := by rw [← map_zero (ι 0), hι.extendUnionFun_apply hξ 0 0, map_zero]
  map_add' := hι.extendUnionFun_map₂ hξ (fun _ ↦ (· + ·)) (· + ·) (· + ·)
    continuous_add continuous_add (fun n ↦ map_add (ι n)) (fun n ↦ map_add (ξ n))
  map_mul' := hι.extendUnionFun_map₂ hξ (fun _ ↦ (· * ·)) (· * ·) (· * ·)
    continuous_mul continuous_mul (fun n ↦ map_mul (ι n)) (fun n ↦ map_mul (ξ n))
  map_smul' c x :=
    let cont := hι.continuous_extendUnionFun hξ
    hι.dense_iUnion_range.denseRange_subtypeVal.induction_on x
      (isClosed_eq (cont.comp (continuous_const_smul c)) ((continuous_const_smul c).comp cont)) <|
      by
        rintro ⟨_, ⟨_, ⟨n, rfl⟩, a, rfl⟩⟩
        dsimp only [MonoidHom.id_apply]
        rw [← map_smul, hι.extendUnionFun_apply hξ, hι.extendUnionFun_apply hξ, map_smul]
  map_star' x :=
    let cont := hι.continuous_extendUnionFun hξ
    hι.dense_iUnion_range.denseRange_subtypeVal.induction_on x
      (isClosed_eq (cont.comp continuous_star) (continuous_star.comp cont)) <| by
      rintro ⟨_, ⟨_, ⟨n, rfl⟩, a, rfl⟩⟩
      dsimp only
      rw [← map_star, hι.extendUnionFun_apply hξ, hι.extendUnionFun_apply hξ, map_star]

/-- Evaluating `hι.lift ξ hξ` on a stage element `ι n a` recovers `ξ n a`. -/
@[simp]
theorem lift_apply {D : Type*} [NonUnitalCStarAlgebra D] (hι : IsSeqColimitCocone α ι)
    (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) (n : ℕ) (a : A n) :
    hι.lift ξ hξ (ι n a) = ξ n a :=
  hι.extendUnionFun_apply hξ n a

/-- Composing `hι.lift ξ hξ` with the `n`-th cocone map recovers `ξ n`. -/
@[simp]
theorem lift_comp {D : Type*} [NonUnitalCStarAlgebra D] (hι : IsSeqColimitCocone α ι)
    (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) (n : ℕ) :
    (hι.lift ξ hξ).comp (ι n) = ξ n :=
  NonUnitalStarAlgHom.ext (hι.lift_apply ξ hξ n)

/-- Uniqueness of the lifted `⋆`-homomorphism out of a sequential colimit cocone. -/
theorem lift_unique {D : Type*} [NonUnitalCStarAlgebra D] (hι : IsSeqColimitCocone α ι)
    {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D} (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n)
    {Φ : C →⋆ₙₐ[ℂ] D} (hΦ : ∀ n a, Φ (ι n a) = ξ n a) :
    Φ = hι.lift ξ hξ :=
  hι.hom_ext fun n a ↦ (hΦ n a).trans (hι.lift_apply ξ hξ n a).symm

/-- Canonical `⋆`-isomorphism between two sequential colimit realizations of the same system. -/
noncomputable def equiv {D : Type*} [NonUnitalCStarAlgebra D] {ι₂ : ∀ n, A n →⋆ₙₐ[ℂ] D}
    (hι : IsSeqColimitCocone α ι) (hι₂ : IsSeqColimitCocone α ι₂) : C ≃⋆ₐ[ℂ] D :=
  StarAlgEquiv.ofNonUnitalStarAlgHom (hι.lift ι₂ hι₂.comp_eq) (hι₂.lift ι hι.comp_eq)
    (hι.hom_ext fun n a ↦ by simp)
    (hι₂.hom_ext fun n a ↦ by simp)

/-- The forward `⋆`-homomorphism underlying `hι.equiv hι₂` is `hι.lift ι₂ hι₂.comp_eq`. -/
@[simp]
theorem toNonUnitalStarAlgHom_equiv {D : Type*} [NonUnitalCStarAlgebra D]
    {ι₂ : ∀ n, A n →⋆ₙₐ[ℂ] D} (hι : IsSeqColimitCocone α ι) (hι₂ : IsSeqColimitCocone α ι₂) :
    (hι.equiv hι₂).toNonUnitalStarAlgHom = hι.lift ι₂ hι₂.comp_eq :=
  StarAlgEquiv.toNonUnitalStarAlgHom_ofNonUnitalStarAlgHom ..

/-- The inverse `⋆`-homomorphism underlying `(hι.equiv hι₂).symm` is `hι₂.lift ι hι.comp_eq`. -/
@[simp]
theorem toNonUnitalStarAlgHom_equiv_symm {D : Type*} [NonUnitalCStarAlgebra D]
    {ι₂ : ∀ n, A n →⋆ₙₐ[ℂ] D} (hι : IsSeqColimitCocone α ι) (hι₂ : IsSeqColimitCocone α ι₂) :
    (hι.equiv hι₂).symm.toNonUnitalStarAlgHom = hι₂.lift ι hι.comp_eq :=
  StarAlgEquiv.toNonUnitalStarAlgHom_symm_ofNonUnitalStarAlgHom ..

/-- Applying the canonical comparison `⋆`-isomorphism `hι.equiv hι₂` to a stage image `ι n a`
yields `ι₂ n a`. -/
@[simp]
theorem equiv_apply {D : Type*} [NonUnitalCStarAlgebra D] {ι₂ : ∀ n, A n →⋆ₙₐ[ℂ] D}
    (hι : IsSeqColimitCocone α ι) (hι₂ : IsSeqColimitCocone α ι₂) (n : ℕ) (a : A n) :
    hι.equiv hι₂ (ι n a) = ι₂ n a :=
  hι.lift_apply ι₂ hι₂.comp_eq n a

/-- Applying the inverse `(hι.equiv hι₂).symm` to a stage image `ι₂ n a` yields `ι n a`. -/
@[simp]
theorem equiv_symm_apply {D : Type*} [NonUnitalCStarAlgebra D] {ι₂ : ∀ n, A n →⋆ₙₐ[ℂ] D}
    (hι : IsSeqColimitCocone α ι) (hι₂ : IsSeqColimitCocone α ι₂) (n : ℕ) (a : A n) :
    (hι.equiv hι₂).symm (ι₂ n a) = ι n a :=
  hι₂.lift_apply ι hι.comp_eq n a

end IsSeqColimitCocone

/-- The concrete C⋆-inductive limit `CStarInductiveLimit` of the sequential system generated by
`α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)` forms a sequential colimit cocone under its canonical stage maps
`CStarInductiveLimit.of`. -/
theorem CStarInductiveLimit.isSeqColimitCocone_of (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) :
    IsSeqColimitCocone α (CStarInductiveLimit.of A (fun _ _ h ↦ seqTransHom α h)) := by
  refine IsSeqColimitCocone.of_norm_eq_ciInf (fun n ↦ ?_)
    (CStarInductiveLimit.dense_iUnion_range_of A (fun _ _ h ↦ seqTransHom α h))
    (fun n a ↦ ?_)
  · ext a
    simp only [NonUnitalStarAlgHom.comp_apply, ← seqTransHom_le_succ α n]
    exact CStarInductiveLimit.of_f (f := fun _ _ h ↦ seqTransHom α h) (Nat.le_succ n) a
  · rw [CStarInductiveLimit.norm_of]
    have hbdd₁ : BddBelow (Set.range fun j : {j // n ≤ j} ↦ ‖seqTransHom α j.property a‖) :=
      ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩
    have hbdd₂ : BddBelow (Set.range fun k ↦ ‖seqTransHom α (Nat.le_add_right n k) a‖) :=
      ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩
    refine le_antisymm (le_ciInf fun k ↦ ?_) (le_ciInf fun ⟨m, hm⟩ ↦ ?_)
    · exact ciInf_le hbdd₁ (⟨n + k, Nat.le_add_right n k⟩ : {j // n ≤ j})
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      exact ciInf_le hbdd₂ k

end TauCeti
