/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import TauCeti.Algebra.Star.DirectedSystem
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Elliott's approximate intertwining of sequential C⋆-systems

Given two sequential inductive systems of (possibly nonunital) C⋆-algebras
`A₀ →[α₀] A₁ →[α₁] ⋯` and `B₀ →[β₀] B₁ →[β₁] ⋯` with possibly noninjective connecting maps and
compatible colimit cones `ιA : ∀ n, A n →⋆ₙₐ[ℂ] C` and `ιB : ∀ n, B n →⋆ₙₐ[ℂ] D`, Elliott's
approximate-intertwining criterion produces a `⋆`-isomorphism `C ≃⋆ₐ[ℂ] D` from stage maps
`φ n : A n →⋆ₙₐ[ℂ] B (n + 1)` and `ψ n : B n →⋆ₙₐ[ℂ] A n` whose triangles commute up to summable
errors on propagating stagewise-dense sets `F n ⊆ A n` and `G n ⊆ B n`.

The construction factors through a one-sided approximate-cocone theorem (`IsApproxCocone.hom`),
which builds a `⋆`-homomorphism `C →⋆ₙₐ[ℂ] D` with a quantitative tail-error bound whenever stage
maps `ξ n : A n →⋆ₙₐ[ℂ] D` satisfy `‖ξ (n + 1) (α n a) - ξ n a‖ ≤ τ n` on `F n` with `Summable τ`,
descending the pointwise limit cocone via the exact universal lift `IsSeqColimitCone.lift`.
Applying `IsApproxCocone.hom` in both directions and checking the two composite identities on
dense stage elements yields `IsApproximateIntertwining.equiv` together with its forward and
backward tail estimates.

## Main definitions and results

* `TauCeti.IsSeqColimitCone` and `TauCeti.IsSeqColimitCone.lift`: predicate characterizing a
  compatible colimit cone into a C⋆-algebra by density of the union of stage images and convergence
  of stage norms along `seqTransHom`, with universal lift `lift` (`lift_apply`, `lift_comp`,
  `lift_unique`), extensionality (`hom_ext`, `hom_ext_of_approx`), and constructors `.const`,
  `.of_isometry`, `.of_subalgebra`, and `.of_norm_eq_ciInf`.
* `TauCeti.IsApproxCocone` and `TauCeti.IsApproxCocone.hom`: one-sided limit `⋆`-homomorphism from
  an approximate cocone, with uniqueness and tail estimate `IsApproxCocone.norm_hom_sub_le`.
* `TauCeti.IsApproximateIntertwining` and `TauCeti.IsApproximateIntertwining.equiv`: two-sided
  approximate intertwining inducing `C ≃⋆ₐ[ℂ] D`, with uniqueness and forward/backward tail
  estimates `norm_equiv_sub_le` and `norm_equiv_symm_sub_le`.

## References

* G. A. Elliott, *On the classification of C⋆-algebras of real rank zero*, J. Reine Angew. Math.
  443 (1993), Theorem 2.1.
* M. Rørdam, *Classification of Nuclear C⋆-Algebras*, Encyclopaedia of Mathematical Sciences 126,
  Springer (2002), §2.3, Proposition 2.3.2.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti

section ColimitCone

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

/-- A compatible cone `ι : ∀ n, A n →⋆ₙₐ[ℂ] C` from a sequential system of C⋆-algebras
`(A, α)` into `C` is a *sequential colimit cone* when `(ι (n + 1)).comp (α n) = ι n` for every
`n`, the union `⋃ n, Set.range (ι n)` is dense in `C`, and `‖seqTransHom α _ a‖ → ‖ι n a‖` as
the offset tends to infinity. Connecting maps `α n` need not be injective. -/
structure IsSeqColimitCone (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1))
    (ι : ∀ n, A n →⋆ₙₐ[ℂ] C) : Prop where
  /-- Compatibility of the cone maps with the connecting maps. -/
  comp_eq (n : ℕ) : (ι (n + 1)).comp (α n) = ι n
  /-- Density of the algebraic union of stage images inside `C`. -/
  dense_iUnion_range : Dense (⋃ n, Set.range (ι n))
  /-- Asymptotic seminorm formula along the connecting maps. -/
  tendsto_norm (n : ℕ) (a : A n) :
    Tendsto (fun k ↦ ‖seqTransHom α (Nat.le_add_right n k) a‖) atTop (𝓝 ‖ι n a‖)

namespace IsSeqColimitCone

variable {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {ι : ∀ n, A n →⋆ₙₐ[ℂ] C}

@[simp]
theorem comp_apply (hι : IsSeqColimitCone α ι) (n : ℕ) (a : A n) :
    ι (n + 1) (α n a) = ι n a :=
  DFunLike.congr_fun (hι.comp_eq n) a

theorem comp_seqTransHom (hι : IsSeqColimitCone α ι) {m n : ℕ} (h : m ≤ n) :
    (ι n).comp (seqTransHom α h) = ι m :=
  comp_seqTransHom_of_comp_eq hι.comp_eq h

@[simp]
theorem comp_seqTransHom_apply (hι : IsSeqColimitCone α ι) {m n : ℕ} (h : m ≤ n) (a : A m) :
    ι n (seqTransHom α h a) = ι m a :=
  DFunLike.congr_fun (hι.comp_seqTransHom h) a

/-- In a sequential colimit cone, the norm in `C` of a stage element is the infimum of its
forward norms along the system. -/
theorem norm_eq_ciInf (hι : IsSeqColimitCone α ι) (n : ℕ) (a : A n) :
    ‖ι n a‖ = ⨅ k, ‖seqTransHom α (Nat.le_add_right n k) a‖ := by
  refine tendsto_nhds_unique (hι.tendsto_norm n a) (tendsto_atTop_ciInf
    (antitone_norm_seqTransHom α n a) ⟨0, ?_⟩)
  rintro _ ⟨k, rfl⟩
  exact norm_nonneg _

/-- Constructor for `IsSeqColimitCone` from the `⨅`-characterization of the limit norm. -/
theorem of_norm_eq_ciInf (hcomp : ∀ n, (ι (n + 1)).comp (α n) = ι n)
    (hdense : Dense (⋃ n, Set.range (ι n)))
    (hnorm : ∀ n a, ‖ι n a‖ = ⨅ k, ‖seqTransHom α (Nat.le_add_right n k) a‖) :
    IsSeqColimitCone α ι where
  comp_eq := hcomp
  dense_iUnion_range := hdense
  tendsto_norm n a := by
    rw [hnorm n a]
    exact tendsto_atTop_ciInf (antitone_norm_seqTransHom α n a)
      ⟨0, by rintro _ ⟨k, rfl⟩; exact norm_nonneg _⟩

/-- The constant system `C →[id] C →[id] ⋯` with identity cone maps is a sequential colimit
cone. -/
theorem const (C : Type*) [NonUnitalCStarAlgebra C] :
    IsSeqColimitCone (A := fun _ ↦ C) (fun _ ↦ .id ℂ C) (fun _ ↦ .id ℂ C) where
  comp_eq _ := rfl
  dense_iUnion_range := by
    have hu : (⋃ _ : ℕ, Set.range (NonUnitalStarAlgHom.id ℂ C)) = Set.univ :=
      Set.iUnion_const _ |>.trans (by simp)
    rw [hu]
    exact dense_univ
  tendsto_norm n a := by
    have hconst (k : ℕ) :
        seqTransHom (A := fun _ ↦ C) (fun _ ↦ .id ℂ C) (Nat.le_add_right n k) a = a := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [seqTransHom_succ _ (Nat.le_add_right n k)]
        exact ih
    simp_rw [hconst]
    exact tendsto_const_nhds

/-- Any compatible cone of isometric `⋆`-homomorphisms whose ranges have dense union is a
sequential colimit cone. -/
theorem of_isometry (hcomp : ∀ n, (ι (n + 1)).comp (α n) = ι n)
    (hdense : Dense (⋃ n, Set.range (ι n))) (hiso : ∀ n a, ‖ι n a‖ = ‖a‖) :
    IsSeqColimitCone α ι where
  comp_eq := hcomp
  dense_iUnion_range := hdense
  tendsto_norm n a := by
    have hnorm (k : ℕ) : ‖seqTransHom α (Nat.le_add_right n k) a‖ = ‖ι n a‖ := by
      rw [← hiso (n + k), comp_seqTransHom_apply_of_comp_eq hcomp]
    simp_rw [hnorm]
    exact tendsto_const_nhds

/-- An increasing sequence of closed C⋆-subalgebras with dense union forms a sequential colimit
cone under subtype inclusions. -/
theorem of_subalgebra {S : ℕ → NonUnitalStarSubalgebra ℂ C} [∀ n, IsClosed (S n : Set C)]
    (hS : Monotone S) (hdense : Dense (⋃ n, (S n : Set C))) :
    IsSeqColimitCone (fun n ↦ NonUnitalStarSubalgebra.inclusion (hS (Nat.le_succ n)))
      (fun n ↦ NonUnitalStarSubalgebraClass.subtype (S n)) := by
  refine of_isometry (fun _ ↦ rfl) ?_ (fun _ _ ↦ rfl)
  have hr (n : ℕ) : Set.range ⇑(NonUnitalStarSubalgebraClass.subtype (S n)) = (S n : Set C) := by
    ext x
    simp
  simp_rw [hr]
  exact hdense

/-- If stage subsets `F n ⊆ A n` asymptotically approximate every stage element along `α`, then
the union of their stage images `⋃ n, ι n '' F n` is dense in `C`. -/
theorem dense_iUnion_image_of_approx (hι : IsSeqColimitCone α ι) {F : ∀ n, Set (A n)}
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
theorem hom_ext_of_approx {D : Type*} [NonUnitalCStarAlgebra D] (hι : IsSeqColimitCone α ι)
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

/-- Two `⋆`-homomorphisms out of `C` that agree on every stage of a sequential colimit cone are
equal. -/
theorem hom_ext {D : Type*} [NonUnitalCStarAlgebra D] (hι : IsSeqColimitCone α ι)
    {Φ₁ Φ₂ : C →⋆ₙₐ[ℂ] D} (h : ∀ n a, Φ₁ (ι n a) = Φ₂ (ι n a)) : Φ₁ = Φ₂ :=
  hι.hom_ext_of_approx (F := fun _ ↦ Set.univ)
    (fun _ a _ hr ↦ ⟨0, a, trivial, by simpa using hr⟩) fun n a _ ↦ h n a

private theorem norm_le_of_comp_eq {D : Type*} [NonUnitalCStarAlgebra D]
    (hι : IsSeqColimitCone α ι) {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D}
    (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) (n : ℕ) (a : A n) : ‖ξ n a‖ ≤ ‖ι n a‖ :=
  ge_of_tendsto' (hι.tendsto_norm n a) fun k ↦ by
    rw [← comp_seqTransHom_apply_of_comp_eq hξ (Nat.le_add_right n k) a]
    exact NonUnitalStarAlgHom.norm_apply_le _ _

/-- Induced contractive map on the dense subtype `↥(⋃ n, Set.range (ι n))`. -/
private noncomputable def unionFun {D : Type*} [NonUnitalCStarAlgebra D]
    (ι : ∀ n, A n →⋆ₙₐ[ℂ] C) (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D) (u : ↥(⋃ n, Set.range (ι n))) : D := by
  classical
  exact ξ (Set.mem_iUnion.mp u.2).choose (Set.mem_iUnion.mp u.2).choose_spec.choose

private theorem unionFun_apply {D : Type*} [NonUnitalCStarAlgebra D]
    (hι : IsSeqColimitCone α ι) {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D}
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
    (hι : IsSeqColimitCone α ι) {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D}
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

/-- Universal property of a sequential colimit cone: any compatible family of stage
`⋆`-homomorphisms `ξ : ∀ n, A n →⋆ₙₐ[ℂ] D` descends to a `⋆`-homomorphism `C →⋆ₙₐ[ℂ] D`. -/
noncomputable def lift {D : Type*} [NonUnitalCStarAlgebra D] (hι : IsSeqColimitCone α ι)
    (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) : C →⋆ₙₐ[ℂ] D := by
  let hd : DenseRange ((↑) : ↥(⋃ n, Set.range (ι n)) → C) :=
    hι.dense_iUnion_range.denseRange_val
  let hi : IsUniformInducing ((↑) : ↥(⋃ n, Set.range (ι n)) → C) :=
    isometry_subtype_coe.isUniformInducing
  have huc : UniformContinuous (unionFun ι ξ) := (hι.lipschitzWith_unionFun hξ).uniformContinuous
  have cont : Continuous ((hi.isDenseInducing hd).extend (unionFun ι ξ)) :=
    (uniformContinuous_uniformly_extend hi hd huc).continuous
  have hext : ∀ u : ↥(⋃ n, Set.range (ι n)),
      (hi.isDenseInducing hd).extend (unionFun ι ξ) ↑u = unionFun ι ξ u :=
    uniformly_extend_of_ind hi hd huc
  have hstage (n : ℕ) (a : A n) :
      (hi.isDenseInducing hd).extend (unionFun ι ξ) (ι n a) = ξ n a := by
    have hu : ι n a ∈ ⋃ m, Set.range (ι m) := Set.mem_iUnion.mpr ⟨n, a, rfl⟩
    exact (hext ⟨ι n a, hu⟩).trans (hι.unionFun_apply hξ n a hu)
  exact
    { toFun := (hi.isDenseInducing hd).extend (unionFun ι ξ)
      map_zero' := by rw [← map_zero (ι 0), hstage 0 0, map_zero]
      map_add' := by
        refine hd.induction_on₂
          (isClosed_eq (cont.comp continuous_add)
            ((cont.comp continuous_fst).add (cont.comp continuous_snd))) ?_
        rintro ⟨_, u₁⟩ ⟨_, u₂⟩
        rcases Set.mem_iUnion.mp u₁ with ⟨n₁, a₁, rfl⟩
        rcases Set.mem_iUnion.mp u₂ with ⟨n₂, a₂, rfl⟩
        dsimp only
        rw [← hι.comp_seqTransHom_apply (le_max_left n₁ n₂) a₁,
          ← hι.comp_seqTransHom_apply (le_max_right n₁ n₂) a₂, ← map_add,
          hstage, hstage, hstage, map_add]
      map_mul' := by
        refine hd.induction_on₂
          (isClosed_eq (cont.comp continuous_mul)
            ((cont.comp continuous_fst).mul (cont.comp continuous_snd))) ?_
        rintro ⟨_, u₁⟩ ⟨_, u₂⟩
        rcases Set.mem_iUnion.mp u₁ with ⟨n₁, a₁, rfl⟩
        rcases Set.mem_iUnion.mp u₂ with ⟨n₂, a₂, rfl⟩
        dsimp only
        rw [← hι.comp_seqTransHom_apply (le_max_left n₁ n₂) a₁,
          ← hι.comp_seqTransHom_apply (le_max_right n₁ n₂) a₂, ← map_mul,
          hstage, hstage, hstage, map_mul]
      map_smul' c x := by
        refine hd.induction_on x
          (isClosed_eq (cont.comp (continuous_const_smul c))
            ((continuous_const_smul c).comp cont)) ?_
        rintro ⟨_, u⟩
        rcases Set.mem_iUnion.mp u with ⟨n, a, rfl⟩
        dsimp only [MonoidHom.id_apply]
        rw [← map_smul, hstage, hstage, map_smul]
      map_star' x := by
        refine hd.induction_on x
          (isClosed_eq (cont.comp continuous_star) (continuous_star.comp cont)) ?_
        rintro ⟨_, u⟩
        rcases Set.mem_iUnion.mp u with ⟨n, a, rfl⟩
        dsimp only
        rw [← map_star, hstage, hstage, map_star] }

/-- Evaluating `hι.lift ξ hξ` on a stage element `ι n a` recovers `ξ n a`. -/
@[simp]
theorem lift_apply {D : Type*} [NonUnitalCStarAlgebra D] (hι : IsSeqColimitCone α ι)
    (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) (n : ℕ) (a : A n) :
    hι.lift ξ hξ (ι n a) = ξ n a := by
  let hd : DenseRange ((↑) : ↥(⋃ m, Set.range (ι m)) → C) :=
    hι.dense_iUnion_range.denseRange_val
  let hi : IsUniformInducing ((↑) : ↥(⋃ m, Set.range (ι m)) → C) :=
    isometry_subtype_coe.isUniformInducing
  have hu : ι n a ∈ ⋃ m, Set.range (ι m) := Set.mem_iUnion.mpr ⟨n, a, rfl⟩
  exact (uniformly_extend_of_ind hi hd
    (hι.lipschitzWith_unionFun hξ).uniformContinuous ⟨ι n a, hu⟩).trans
    (hι.unionFun_apply hξ n a hu)

/-- Composing `hι.lift ξ hξ` with the `n`-th cone map recovers `ξ n`. -/
@[simp]
theorem lift_comp {D : Type*} [NonUnitalCStarAlgebra D] (hι : IsSeqColimitCone α ι)
    (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n) (n : ℕ) :
    (hι.lift ξ hξ).comp (ι n) = ξ n :=
  NonUnitalStarAlgHom.ext (hι.lift_apply ξ hξ n)

/-- Uniqueness of the lifted `⋆`-homomorphism out of a sequential colimit cone. -/
theorem lift_unique {D : Type*} [NonUnitalCStarAlgebra D] (hι : IsSeqColimitCone α ι)
    {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D} (hξ : ∀ n, (ξ (n + 1)).comp (α n) = ξ n)
    {Φ : C →⋆ₙₐ[ℂ] D} (hΦ : ∀ n a, Φ (ι n a) = ξ n a) :
    Φ = hι.lift ξ hξ :=
  hι.hom_ext fun n a ↦ (hΦ n a).trans (hι.lift_apply ξ hξ n a).symm

end IsSeqColimitCone

end ColimitCone

section ApproxCocone

variable {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)]
  {C D : Type*} [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

/-- Stage maps `ξ : ∀ n, A n →⋆ₙₐ[ℂ] D` form an *approximate cocone* on a sequential C⋆-system
`(A, α)` relative to propagating subsets `F n ⊆ A n` and summable step tolerances `τ : ℕ → ℝ` when
every stage element can be approximated to arbitrary accuracy in some later `F (n + k)` and
`‖ξ (n + 1) (α n a) - ξ n a‖ ≤ τ n` on `F n`. -/
structure IsApproxCocone (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D)
    (F : ∀ n, Set (A n)) (τ : ℕ → ℝ) : Prop where
  /-- Forward propagation of the approximating subsets along `α`. -/
  mapsTo (n : ℕ) ⦃a : A n⦄ : a ∈ F n → α n a ∈ F (n + 1)
  /-- Asymptotic stagewise density of `(F n)` along `α`. -/
  approx (n : ℕ) (a : A n) (ε : ℝ) :
    0 < ε → ∃ k, ∃ x ∈ F (n + k), ‖seqTransHom α (Nat.le_add_right n k) a - x‖ < ε
  /-- Stepwise Cauchy estimate on `F n`. -/
  norm_sub_le (n : ℕ) ⦃a : A n⦄ : a ∈ F n → ‖ξ (n + 1) (α n a) - ξ n a‖ ≤ τ n
  /-- Summability of the step tolerances. -/
  summable : Summable τ

namespace IsApproxCocone

variable {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {ι : ∀ n, A n →⋆ₙₐ[ℂ] C}
  {ξ : ∀ n, A n →⋆ₙₐ[ℂ] D} {F : ∀ n, Set (A n)} {τ : ℕ → ℝ}

/-- Absolute-stage evaluation sequence `m ↦ ξ m (seqTransHom α h a)` (zero for `m < n`), avoiding
dependent index casts when comparing elements from different stages. -/
private noncomputable def evalAt (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (ξ : ∀ n, A n →⋆ₙₐ[ℂ] D)
    {n : ℕ} (a : A n) (m : ℕ) : D :=
  if h : n ≤ m then ξ m (seqTransHom α h a) else 0

private theorem evalAt_of_le {n m : ℕ} (h : n ≤ m) (a : A n) :
    evalAt α ξ a m = ξ m (seqTransHom α h a) := by
  simp [evalAt, h]

private theorem evalAt_add (n k : ℕ) (a : A n) :
    evalAt α ξ a (n + k) = ξ (n + k) (seqTransHom α (Nat.le_add_right n k) a) := by
  simp [evalAt]

private theorem evalAt_eventuallyEq_seqTransHom {m n : ℕ} (h : m ≤ n) (a : A m) :
    evalAt α ξ (seqTransHom α h a) =ᶠ[atTop] evalAt α ξ a := by
  filter_upwards [eventually_ge_atTop n] with k hk
  rw [evalAt_of_le hk, evalAt_of_le (h.trans hk), seqTransHom_comp_apply]

private theorem cauchySeq_offset_of_mem (hc : IsApproxCocone α ξ F τ) {n : ℕ} {x : A n}
    (hx : x ∈ F n) :
    CauchySeq (fun k ↦ ξ (n + k) (seqTransHom α (Nat.le_add_right n k) x)) := by
  have hτ : Summable (fun k ↦ τ (n + k)) :=
    ((summable_nat_add_iff n).mpr hc.summable).congr fun k ↦ by rw [Nat.add_comm]
  refine cauchySeq_of_dist_le_of_summable (fun k ↦ τ (n + k)) (fun k ↦ ?_) hτ
  have hxk : seqTransHom α (Nat.le_add_right n k) x ∈ F (n + k) :=
    seqTransHom_mem hc.mapsTo (Nat.le_add_right n k) hx
  rw [dist_eq_norm, norm_sub_rev, seqTransHom_succ α (Nat.le_add_right n k)]
  exact hc.norm_sub_le (n + k) hxk

private theorem cauchySeq_evalAt (hc : IsApproxCocone α ξ F τ) (n : ℕ) (a : A n) :
    CauchySeq (evalAt α ξ a) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨k₀, x, hxF, hax⟩ := hc.approx n a (ε / 3) (by positivity)
  obtain ⟨N₀, hN₀⟩ :=
    Metric.cauchySeq_iff.mp (hc.cauchySeq_offset_of_mem hxF) (ε / 3) (by positivity)
  refine ⟨n + k₀ + N₀, fun p hp q hq ↦ ?_⟩
  have hclose (r : ℕ) (hr : n + k₀ + N₀ ≤ r) :
      dist (evalAt α ξ a r)
        (ξ (n + k₀ + (r - (n + k₀)))
          (seqTransHom α (Nat.le_add_right (n + k₀) (r - (n + k₀))) x)) < ε / 3 := by
    have hnr : n ≤ r := by omega
    have hnkr : n + k₀ ≤ r := by omega
    have heq : evalAt α ξ x r =
        ξ (n + k₀ + (r - (n + k₀)))
          (seqTransHom α (Nat.le_add_right (n + k₀) (r - (n + k₀))) x) := by
      have hr' : n + k₀ + (r - (n + k₀)) = r := Nat.add_sub_of_le hnkr
      rw [← evalAt_add (n + k₀) (r - (n + k₀)) x, hr']
    rw [← heq, evalAt_of_le hnr, evalAt_of_le hnkr,
      ← seqTransHom_comp_apply α (Nat.le_add_right n k₀) hnkr a, dist_eq_norm,
      ← map_sub, ← map_sub]
    exact (le_trans (NonUnitalStarAlgHom.norm_apply_le _ _)
      (NonUnitalStarAlgHom.norm_apply_le _ _)).trans_lt hax
  calc
    dist (evalAt α ξ a p) (evalAt α ξ a q)
      ≤ dist (evalAt α ξ a p)
          (ξ (n + k₀ + (p - (n + k₀)))
            (seqTransHom α (Nat.le_add_right (n + k₀) (p - (n + k₀))) x)) +
        dist
          (ξ (n + k₀ + (p - (n + k₀)))
            (seqTransHom α (Nat.le_add_right (n + k₀) (p - (n + k₀))) x))
          (ξ (n + k₀ + (q - (n + k₀)))
            (seqTransHom α (Nat.le_add_right (n + k₀) (q - (n + k₀))) x)) +
        dist
          (ξ (n + k₀ + (q - (n + k₀)))
            (seqTransHom α (Nat.le_add_right (n + k₀) (q - (n + k₀))) x))
          (evalAt α ξ a q) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add (hclose p hp)
        (hN₀ _ (by omega) _ (by omega))) (by rw [dist_comm]; exact hclose q hq)
    _ = ε := by ring

private noncomputable def stageLim (hc : IsApproxCocone α ξ F τ) {n : ℕ} (a : A n) : D :=
  (cauchySeq_tendsto_of_complete (hc.cauchySeq_evalAt n a)).choose

private theorem tendsto_evalAt_stageLim (hc : IsApproxCocone α ξ F τ) (n : ℕ) (a : A n) :
    Tendsto (evalAt α ξ a) atTop (𝓝 (hc.stageLim a)) :=
  (cauchySeq_tendsto_of_complete (hc.cauchySeq_evalAt n a)).choose_spec

/-- Stagewise limit `⋆`-homomorphism `A n →⋆ₙₐ[ℂ] D` constructed from an approximate cocone. -/
private noncomputable def stageHom (hc : IsApproxCocone α ξ F τ) (n : ℕ) : A n →⋆ₙₐ[ℂ] D where
  toFun a := hc.stageLim a
  map_zero' := tendsto_nhds_unique (hc.tendsto_evalAt_stageLim n 0) <| by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    simp [evalAt_of_le hm]
  map_add' a b := by
    refine tendsto_nhds_unique (hc.tendsto_evalAt_stageLim n (a + b))
      (((hc.tendsto_evalAt_stageLim n a).add (hc.tendsto_evalAt_stageLim n b)).congr' ?_)
    filter_upwards [eventually_ge_atTop n] with m hm
    simp [evalAt_of_le hm]
  map_mul' a b := by
    refine tendsto_nhds_unique (hc.tendsto_evalAt_stageLim n (a * b))
      (((hc.tendsto_evalAt_stageLim n a).mul (hc.tendsto_evalAt_stageLim n b)).congr' ?_)
    filter_upwards [eventually_ge_atTop n] with m hm
    simp [evalAt_of_le hm]
  map_smul' c a := by
    refine tendsto_nhds_unique (hc.tendsto_evalAt_stageLim n (c • a))
      (((hc.tendsto_evalAt_stageLim n a).const_smul c).congr' ?_)
    filter_upwards [eventually_ge_atTop n] with m hm
    simp [evalAt_of_le hm]
  map_star' a := by
    refine tendsto_nhds_unique (hc.tendsto_evalAt_stageLim n (star a))
      ((hc.tendsto_evalAt_stageLim n a).star.congr' ?_)
    filter_upwards [eventually_ge_atTop n] with m hm
    simp [evalAt_of_le hm, map_star]

private theorem tendsto_evalAt_stageHom (hc : IsApproxCocone α ξ F τ) (n : ℕ) (a : A n) :
    Tendsto (evalAt α ξ a) atTop (𝓝 (hc.stageHom n a)) :=
  hc.tendsto_evalAt_stageLim n a

private theorem tendsto_stageHom (hc : IsApproxCocone α ξ F τ) (n : ℕ) (a : A n) :
    Tendsto (fun k ↦ ξ (n + k) (seqTransHom α (Nat.le_add_right n k) a))
      atTop (𝓝 (hc.stageHom n a)) := by
  have hshift : Tendsto (fun k ↦ n + k) atTop atTop :=
    (tendsto_add_atTop_nat n).congr fun k ↦ Nat.add_comm k n
  have h := (hc.tendsto_evalAt_stageHom n a).comp hshift
  simpa only [Function.comp_def, evalAt_add] using h

private theorem stageHom_seqTransHom (hc : IsApproxCocone α ξ F τ) {m n : ℕ} (h : m ≤ n)
    (a : A m) : hc.stageHom n (seqTransHom α h a) = hc.stageHom m a :=
  tendsto_nhds_unique (hc.tendsto_evalAt_stageHom n _)
    ((hc.tendsto_evalAt_stageHom m a).congr' (evalAt_eventuallyEq_seqTransHom h a).symm)

private theorem stageHom_comp (hc : IsApproxCocone α ξ F τ) (n : ℕ) :
    (hc.stageHom (n + 1)).comp (α n) = hc.stageHom n := by
  ext a
  simpa only [NonUnitalStarAlgHom.comp_apply, seqTransHom_le_succ] using
    hc.stageHom_seqTransHom (Nat.le_succ n) a

/-- The `⋆`-homomorphism `C →⋆ₙₐ[ℂ] D` induced by an approximate cocone on a sequential colimit
cone. -/
noncomputable def hom (hc : IsApproxCocone α ξ F τ) (hι : IsSeqColimitCone α ι) :
    C →⋆ₙₐ[ℂ] D :=
  hι.lift hc.stageHom hc.stageHom_comp

/-- On every stage element `a : A n`, the forward images `ξ (n + k) (seqTransHom α _ a)` converge
in norm to `hc.hom hι (ι n a)`. -/
theorem tendsto_hom (hc : IsApproxCocone α ξ F τ) (hι : IsSeqColimitCone α ι)
    (n : ℕ) (a : A n) :
    Tendsto (fun k ↦ ξ (n + k) (seqTransHom α (Nat.le_add_right n k) a))
      atTop (𝓝 (hc.hom hι (ι n a))) := by
  rw [hom, hι.lift_apply]
  exact hc.tendsto_stageHom n a

/-- Uniqueness of the limit `⋆`-homomorphism induced by an approximate cocone. -/
theorem hom_unique (hc : IsApproxCocone α ξ F τ) (hι : IsSeqColimitCone α ι)
    {Φ : C →⋆ₙₐ[ℂ] D}
    (hΦ : ∀ n a, Tendsto (fun k ↦ ξ (n + k) (seqTransHom α (Nat.le_add_right n k) a))
      atTop (𝓝 (Φ (ι n a)))) :
    Φ = hc.hom hι :=
  hι.hom_ext fun n a ↦ tendsto_nhds_unique (hΦ n a) (hc.tendsto_hom hι n a)

/-- Quantitative tail-error bound: on `a ∈ F n`, `hc.hom hι (ι n a)` is within `∑' k, τ (n + k)`
of the stage map `ξ n a`. -/
theorem norm_hom_sub_le (hc : IsApproxCocone α ξ F τ) (hι : IsSeqColimitCone α ι)
    {n : ℕ} {a : A n} (ha : a ∈ F n) :
    ‖hc.hom hι (ι n a) - ξ n a‖ ≤ ∑' k, τ (n + k) := by
  have h0 : ξ (n + 0) (seqTransHom α (Nat.le_add_right n 0) a) = ξ n a := by simp
  have hτ : Summable (fun k ↦ τ (n + k)) :=
    ((summable_nat_add_iff n).mpr hc.summable).congr fun k ↦ by rw [Nat.add_comm]
  rw [norm_sub_rev, ← dist_eq_norm, ← h0]
  refine dist_le_tsum_of_dist_le_of_tendsto₀ (fun k ↦ τ (n + k)) (fun k ↦ ?_) hτ
    (hc.tendsto_hom hι n a)
  have hak : seqTransHom α (Nat.le_add_right n k) a ∈ F (n + k) :=
    seqTransHom_mem hc.mapsTo (Nat.le_add_right n k) ha
  rw [dist_eq_norm, norm_sub_rev, seqTransHom_succ α (Nat.le_add_right n k)]
  exact hc.norm_sub_le (n + k) hak

end IsApproxCocone

end ApproxCocone

section Intertwining

variable {A B : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)] [∀ n, NonUnitalCStarAlgebra (B n)]
  {C D : Type*} [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

/-- An *approximate intertwining* between sequential C⋆-systems `(A, α)` and `(B, β)` consists of
stage maps `φ n : A n →⋆ₙₐ[ℂ] B (n + 1)` and `ψ n : B n →⋆ₙₐ[ℂ] A n`, propagating subsets
`F n ⊆ A n` and `G n ⊆ B n` that asymptotically approximate every stage element, and summable
triangle tolerances `δ, ε : ℕ → ℝ` bounding `‖ψ (n + 1) (φ n a) - α n a‖ ≤ δ n` on `F n` and
`‖φ n (ψ n b) - β n b‖ ≤ ε n` on `G n` (Rørdam, *Classification of Nuclear C⋆-Algebras*,
Proposition 2.3.2). -/
structure IsApproximateIntertwining
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (F : ∀ n, Set (A n)) (G : ∀ n, Set (B n)) (δ ε : ℕ → ℝ) : Prop where
  /-- Forward propagation of `F` along `α`. -/
  mapsTo_α (n : ℕ) ⦃a : A n⦄ : a ∈ F n → α n a ∈ F (n + 1)
  /-- Forward propagation of `G` along `β`. -/
  mapsTo_β (n : ℕ) ⦃b : B n⦄ : b ∈ G n → β n b ∈ G (n + 1)
  /-- Propagation from `F n` into `G (n + 1)` under `φ n`. -/
  mapsTo_φ (n : ℕ) ⦃a : A n⦄ : a ∈ F n → φ n a ∈ G (n + 1)
  /-- Propagation from `G n` into `F n` under `ψ n`. -/
  mapsTo_ψ (n : ℕ) ⦃b : B n⦄ : b ∈ G n → ψ n b ∈ F n
  /-- Asymptotic stagewise density of `(F n)` along `α`. -/
  approx_A (n : ℕ) (a : A n) (r : ℝ) :
    0 < r → ∃ k, ∃ x ∈ F (n + k), ‖seqTransHom α (Nat.le_add_right n k) a - x‖ < r
  /-- Asymptotic stagewise density of `(G n)` along `β`. -/
  approx_B (n : ℕ) (b : B n) (r : ℝ) :
    0 < r → ∃ k, ∃ y ∈ G (n + k), ‖seqTransHom β (Nat.le_add_right n k) b - y‖ < r
  /-- Upper-triangle commutation estimate on `F n`. -/
  norm_ψ_φ_sub_le (n : ℕ) ⦃a : A n⦄ : a ∈ F n → ‖ψ (n + 1) (φ n a) - α n a‖ ≤ δ n
  /-- Lower-triangle commutation estimate on `G n`. -/
  norm_φ_ψ_sub_le (n : ℕ) ⦃b : B n⦄ : b ∈ G n → ‖φ n (ψ n b) - β n b‖ ≤ ε n
  /-- Summability of the upper-triangle tolerances `δ`. -/
  summable_δ : Summable δ
  /-- Summability of the lower-triangle tolerances `ε`. -/
  summable_ε : Summable ε

namespace IsApproximateIntertwining

variable {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1)}
  {ιA : ∀ n, A n →⋆ₙₐ[ℂ] C} {ιB : ∀ n, B n →⋆ₙₐ[ℂ] D}
  {φ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)} {ψ : ∀ n, B n →⋆ₙₐ[ℂ] A n}
  {F : ∀ n, Set (A n)} {G : ∀ n, Set (B n)} {δ ε : ℕ → ℝ}

/-- The forward stage maps `(ιB (n + 1)).comp (φ n)` form an approximate cocone on `(A, α)` with
step error `δ n + ε (n + 1)`. -/
theorem forwardApproxCocone (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιB : IsSeqColimitCone β ιB) :
    IsApproxCocone α (fun n ↦ (ιB (n + 1)).comp (φ n)) F (fun n ↦ δ n + ε (n + 1)) where
  mapsTo := h.mapsTo_α
  approx := h.approx_A
  summable := h.summable_δ.add ((summable_nat_add_iff 1).mpr h.summable_ε)
  norm_sub_le n a ha := by
    simp only [NonUnitalStarAlgHom.comp_apply]
    rw [← hιB.comp_apply (n + 1) (φ n a), ← map_sub]
    refine (NonUnitalStarAlgHom.norm_apply_le _ _).trans ?_
    calc
      ‖φ (n + 1) (α n a) - β (n + 1) (φ n a)‖
        ≤ ‖φ (n + 1) (α n a) - φ (n + 1) (ψ (n + 1) (φ n a))‖ +
            ‖φ (n + 1) (ψ (n + 1) (φ n a)) - β (n + 1) (φ n a)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖ψ (n + 1) (φ n a) - α n a‖ + ‖φ (n + 1) (ψ (n + 1) (φ n a)) - β (n + 1) (φ n a)‖ := by
          rw [← map_sub, norm_sub_rev (ψ (n + 1) (φ n a))]
          gcongr
          exact NonUnitalStarAlgHom.norm_apply_le _ _
      _ ≤ δ n + ε (n + 1) :=
          add_le_add (h.norm_ψ_φ_sub_le n ha) (h.norm_φ_ψ_sub_le (n + 1) (h.mapsTo_φ n ha))

/-- The backward stage maps `(ιA n).comp (ψ n)` form an approximate cocone on `(B, β)` with step
error `ε n + δ n`. -/
theorem backwardApproxCocone (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCone α ιA) :
    IsApproxCocone β (fun n ↦ (ιA n).comp (ψ n)) G (fun n ↦ ε n + δ n) where
  mapsTo := h.mapsTo_β
  approx := h.approx_B
  summable := h.summable_ε.add h.summable_δ
  norm_sub_le n b hb := by
    simp only [NonUnitalStarAlgHom.comp_apply]
    rw [← hιA.comp_apply n (ψ n b), ← map_sub]
    refine (NonUnitalStarAlgHom.norm_apply_le _ _).trans ?_
    calc
      ‖ψ (n + 1) (β n b) - α n (ψ n b)‖
        ≤ ‖ψ (n + 1) (β n b) - ψ (n + 1) (φ n (ψ n b))‖ +
            ‖ψ (n + 1) (φ n (ψ n b)) - α n (ψ n b)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖φ n (ψ n b) - β n b‖ + ‖ψ (n + 1) (φ n (ψ n b)) - α n (ψ n b)‖ := by
          rw [← map_sub, norm_sub_rev (φ n (ψ n b))]
          gcongr
          exact NonUnitalStarAlgHom.norm_apply_le _ _
      _ ≤ ε n + δ n :=
          add_le_add (h.norm_φ_ψ_sub_le n hb) (h.norm_ψ_φ_sub_le n (h.mapsTo_ψ n hb))

private theorem backward_comp_forward (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCone α ιA) (hιB : IsSeqColimitCone β ιB) :
    ((h.backwardApproxCocone hιA).hom hιB).comp ((h.forwardApproxCocone hιB).hom hιA) =
      .id ℂ C := by
  set Φ := (h.forwardApproxCocone hιB).hom hιA
  set Ψ := (h.backwardApproxCocone hιA).hom hιB
  have hmem_eq {m : ℕ} {x : A m} (hx : x ∈ F m) : Ψ (Φ (ιA m x)) = ιA m x := by
    have hlim₁ : Tendsto
        (fun k ↦ Ψ (ιB (m + k + 1) (φ (m + k) (seqTransHom α (Nat.le_add_right m k) x))))
        atTop (𝓝 (Ψ (Φ (ιA m x)))) :=
      (map_continuous Ψ).continuousAt.tendsto.comp
        ((h.forwardApproxCocone hιB).tendsto_hom hιA m x)
    have hlim₂ : Tendsto
        (fun k ↦ Ψ (ιB (m + k + 1) (φ (m + k) (seqTransHom α (Nat.le_add_right m k) x))))
        atTop (𝓝 (ιA m x)) := by
      rw [← tendsto_sub_nhds_zero_iff]
      refine squeeze_zero_norm (a := fun k ↦
        (∑' j, (ε (j + (m + k + 1)) + δ (j + (m + k + 1)))) + δ (m + k)) (fun k ↦ ?_) ?_
      · have hxk : seqTransHom α (Nat.le_add_right m k) x ∈ F (m + k) :=
          seqTransHom_mem h.mapsTo_α (Nat.le_add_right m k) hx
        have hφk : φ (m + k) (seqTransHom α (Nat.le_add_right m k) x) ∈ G (m + k + 1) :=
          h.mapsTo_φ (m + k) hxk
        have htail := (h.backwardApproxCocone hιA).norm_hom_sub_le hιB hφk
        have htri : ‖ιA (m + k + 1)
            (ψ (m + k + 1) (φ (m + k) (seqTransHom α (Nat.le_add_right m k) x))) - ιA m x‖ ≤
            δ (m + k) := by
          rw [← hιA.comp_seqTransHom_apply (Nat.le_add_right m k) x,
            ← hιA.comp_apply (m + k), ← map_sub]
          exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans (h.norm_ψ_φ_sub_le (m + k) hxk)
        have htsum_eq : (∑' j, (ε (m + k + 1 + j) + δ (m + k + 1 + j))) =
            ∑' j, (ε (j + (m + k + 1)) + δ (j + (m + k + 1))) :=
          tsum_congr fun j ↦ by rw [Nat.add_comm]
        calc
          ‖Ψ (ιB (m + k + 1) (φ (m + k) (seqTransHom α (Nat.le_add_right m k) x))) - ιA m x‖
            ≤ ‖Ψ (ιB (m + k + 1) (φ (m + k) (seqTransHom α (Nat.le_add_right m k) x))) -
                ιA (m + k + 1)
                  (ψ (m + k + 1) (φ (m + k) (seqTransHom α (Nat.le_add_right m k) x)))‖ +
              ‖ιA (m + k + 1)
                (ψ (m + k + 1) (φ (m + k) (seqTransHom α (Nat.le_add_right m k) x))) -
                ιA m x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ _ := add_le_add (htsum_eq ▸ htail) htri
      · have hshift₁ : Tendsto (fun k ↦ m + k + 1) atTop atTop :=
          (tendsto_add_atTop_nat (m + 1)).congr fun k ↦ by omega
        have hshift₂ : Tendsto (fun k ↦ m + k) atTop atTop :=
          (tendsto_add_atTop_nat m).congr fun k ↦ Nat.add_comm k m
        simpa only [Function.comp_def, add_zero] using
          ((_root_.tendsto_sum_nat_add fun i ↦ ε i + δ i).comp hshift₁).add
          (h.summable_δ.tendsto_atTop_zero.comp hshift₂)
    exact tendsto_nhds_unique hlim₁ hlim₂
  exact hιA.hom_ext_of_approx h.approx_A fun _ _ hx ↦ hmem_eq hx

private theorem forward_comp_backward (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCone α ιA) (hιB : IsSeqColimitCone β ιB) :
    ((h.forwardApproxCocone hιB).hom hιA).comp ((h.backwardApproxCocone hιA).hom hιB) =
      .id ℂ D := by
  set Φ := (h.forwardApproxCocone hιB).hom hιA
  set Ψ := (h.backwardApproxCocone hιA).hom hιB
  have hmem_eq {m : ℕ} {y : B m} (hy : y ∈ G m) : Φ (Ψ (ιB m y)) = ιB m y := by
    have hlim₁ : Tendsto
        (fun k ↦ Φ (ιA (m + k) (ψ (m + k) (seqTransHom β (Nat.le_add_right m k) y))))
        atTop (𝓝 (Φ (Ψ (ιB m y)))) :=
      (map_continuous Φ).continuousAt.tendsto.comp
        ((h.backwardApproxCocone hιA).tendsto_hom hιB m y)
    have hlim₂ : Tendsto
        (fun k ↦ Φ (ιA (m + k) (ψ (m + k) (seqTransHom β (Nat.le_add_right m k) y))))
        atTop (𝓝 (ιB m y)) := by
      rw [← tendsto_sub_nhds_zero_iff]
      refine squeeze_zero_norm (a := fun k ↦
        (∑' j, (δ (j + (m + k)) + ε (j + (m + k) + 1))) + ε (m + k)) (fun k ↦ ?_) ?_
      · have hyk : seqTransHom β (Nat.le_add_right m k) y ∈ G (m + k) :=
          seqTransHom_mem h.mapsTo_β (Nat.le_add_right m k) hy
        have hψk : ψ (m + k) (seqTransHom β (Nat.le_add_right m k) y) ∈ F (m + k) :=
          h.mapsTo_ψ (m + k) hyk
        have htail := (h.forwardApproxCocone hιB).norm_hom_sub_le hιA hψk
        have htri : ‖ιB (m + k + 1)
            (φ (m + k) (ψ (m + k) (seqTransHom β (Nat.le_add_right m k) y))) - ιB m y‖ ≤
            ε (m + k) := by
          rw [← hιB.comp_seqTransHom_apply (Nat.le_add_right m k) y,
            ← hιB.comp_apply (m + k), ← map_sub]
          exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans (h.norm_φ_ψ_sub_le (m + k) hyk)
        have htsum_eq : (∑' j, (δ (m + k + j) + ε (m + k + j + 1))) =
            ∑' j, (δ (j + (m + k)) + ε (j + (m + k) + 1)) :=
          tsum_congr fun j ↦ by rw [Nat.add_comm (m + k) j]
        calc
          ‖Φ (ιA (m + k) (ψ (m + k) (seqTransHom β (Nat.le_add_right m k) y))) - ιB m y‖
            ≤ ‖Φ (ιA (m + k) (ψ (m + k) (seqTransHom β (Nat.le_add_right m k) y))) -
                ιB (m + k + 1)
                  (φ (m + k) (ψ (m + k) (seqTransHom β (Nat.le_add_right m k) y)))‖ +
              ‖ιB (m + k + 1)
                (φ (m + k) (ψ (m + k) (seqTransHom β (Nat.le_add_right m k) y))) -
                ιB m y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ _ := add_le_add (htsum_eq ▸ htail) htri
      · have hshift : Tendsto (fun k ↦ m + k) atTop atTop :=
          (tendsto_add_atTop_nat m).congr fun k ↦ Nat.add_comm k m
        simpa only [Function.comp_def, add_zero] using
          ((_root_.tendsto_sum_nat_add fun i ↦ δ i + ε (i + 1)).comp hshift).add
          (h.summable_ε.tendsto_atTop_zero.comp hshift)
    exact tendsto_nhds_unique hlim₁ hlim₂
  exact hιB.hom_ext_of_approx h.approx_B fun _ _ hy ↦ hmem_eq hy

/-- Elliott's approximate-intertwining `⋆`-isomorphism `C ≃⋆ₐ[ℂ] D` constructed from mutually
inverse forward and backward approximate cocones (Rørdam, Proposition 2.3.2). -/
noncomputable def equiv (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCone α ιA) (hιB : IsSeqColimitCone β ιB) : C ≃⋆ₐ[ℂ] D :=
  StarAlgEquiv.ofNonUnitalStarAlgHom
    ((h.forwardApproxCocone hιB).hom hιA)
    ((h.backwardApproxCocone hιA).hom hιB)
    (h.backward_comp_forward hιA hιB)
    (h.forward_comp_backward hιA hιB)

@[simp]
theorem toNonUnitalStarAlgHom_equiv (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCone α ιA) (hιB : IsSeqColimitCone β ιB) :
    (h.equiv hιA hιB).toNonUnitalStarAlgHom = (h.forwardApproxCocone hιB).hom hιA :=
  (rfl)

@[simp]
theorem toNonUnitalStarAlgHom_equiv_symm (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCone α ιA) (hιB : IsSeqColimitCone β ιB) :
    (h.equiv hιA hιB).symm.toNonUnitalStarAlgHom = (h.backwardApproxCocone hιA).hom hιB :=
  (rfl)

/-- Forward stagewise convergence characterizing `IsApproximateIntertwining.equiv`. -/
theorem tendsto_equiv (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCone α ιA) (hιB : IsSeqColimitCone β ιB) (n : ℕ) (a : A n) :
    Tendsto (fun k ↦ ιB (n + k + 1) (φ (n + k) (seqTransHom α (Nat.le_add_right n k) a)))
      atTop (𝓝 (h.equiv hιA hιB (ιA n a))) :=
  (h.forwardApproxCocone hιB).tendsto_hom hιA n a

/-- Backward stagewise convergence characterizing `(IsApproximateIntertwining.equiv).symm`. -/
theorem tendsto_equiv_symm (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCone α ιA) (hιB : IsSeqColimitCone β ιB) (n : ℕ) (b : B n) :
    Tendsto (fun k ↦ ιA (n + k) (ψ (n + k) (seqTransHom β (Nat.le_add_right n k) b)))
      atTop (𝓝 ((h.equiv hιA hιB).symm (ιB n b))) :=
  (h.backwardApproxCocone hιA).tendsto_hom hιB n b

/-- Uniqueness of the `⋆`-isomorphism induced by an approximate intertwining. -/
theorem equiv_unique (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCone α ιA) (hιB : IsSeqColimitCone β ιB)
    {θ : C ≃⋆ₐ[ℂ] D}
    (hθ : ∀ n a, Tendsto
      (fun k ↦ ιB (n + k + 1) (φ (n + k) (seqTransHom α (Nat.le_add_right n k) a)))
      atTop (𝓝 (θ (ιA n a)))) :
    θ = h.equiv hιA hιB := by
  have heq : θ.toNonUnitalStarAlgHom = (h.equiv hιA hιB).toNonUnitalStarAlgHom :=
    (h.forwardApproxCocone hιB).hom_unique hιA hθ
  ext x
  exact DFunLike.congr_fun heq x

/-- Quantitative forward tail-error bound: on `a ∈ F n`, `h.equiv hιA hιB (ιA n a)` is within
`∑' k, (δ (n + k) + ε (n + k + 1))` of `ιB (n + 1) (φ n a)`. -/
theorem norm_equiv_sub_le (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCone α ιA) (hιB : IsSeqColimitCone β ιB) {n : ℕ} {a : A n}
    (ha : a ∈ F n) :
    ‖h.equiv hιA hιB (ιA n a) - ιB (n + 1) (φ n a)‖ ≤ ∑' k, (δ (n + k) + ε (n + k + 1)) :=
  (h.forwardApproxCocone hιB).norm_hom_sub_le hιA ha

/-- Quantitative backward tail-error bound: on `b ∈ G n`, `(h.equiv hιA hιB).symm (ιB n b)` is
within `∑' k, (ε (n + k) + δ (n + k))` of `ιA n (ψ n b)`. -/
theorem norm_equiv_symm_sub_le (h : IsApproximateIntertwining α β φ ψ F G δ ε)
    (hιA : IsSeqColimitCone α ιA) (hιB : IsSeqColimitCone β ιB) {n : ℕ} {b : B n}
    (hb : b ∈ G n) :
    ‖(h.equiv hιA hιB).symm (ιB n b) - ιA n (ψ n b)‖ ≤ ∑' k, (ε (n + k) + δ (n + k)) :=
  (h.backwardApproxCocone hιA).norm_hom_sub_le hιB hb

end IsApproximateIntertwining

end Intertwining

end TauCeti
