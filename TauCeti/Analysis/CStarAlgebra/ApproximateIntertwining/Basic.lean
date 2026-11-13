/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import TauCeti.Topology.Algebra.NonUnitalStarAlgebra

/-!
# Elliott's sequential approximate intertwining

This file develops the analytic approximate-intertwining machinery for sequential inductive
systems of possibly nonunital complex C⋆-algebras with possibly noninjective connecting
`⋆`-homomorphisms.

## Main results

* `NonUnitalStarAlgHom.natLERec`: composes one-step connecting maps `α n : A n →⋆ₙₐ[R] A (n + 1)`
  into multi-step transition maps `A m →⋆ₙₐ[R] A n` for `m ≤ n`.
* `TauCeti.IsSequentialCStarLimit`: characterizes a C⋆-algebra `C` as the C⋆-inductive limit of
  `(A, α)` via compatible `⋆`-homomorphisms `ι n : A n →⋆ₙₐ[ℂ] C` whose ranges have dense union
  and satisfy `‖ι n x‖ = lim_{k → ∞} ‖α_{n, n+k} x‖` (equivalently `‖ι n x‖ = ⨅ k, ‖α_{n, n+k} x‖`).
* `TauCeti.IsSequentialCStarLimit.homOfApprox`: constructs a limit `⋆`-homomorphism `C →⋆ₙₐ[ℂ] D`
  from an approximate cocone `μ n : A n →⋆ₙₐ[ℂ] D` with summable errors on propagating subsets
  that approximate every stage element at later stages, together with forward-image convergence and
  tail-error bounds.
* `TauCeti.ApproximateIntertwining`: packages a two-sided sequential approximate intertwining
  between `(A, α)` and `(B, β)` and constructs the induced `⋆`-isomorphism `C ≃⋆ₐ[ℂ] D`
  (`ApproximateIntertwining.equiv`) with explicit forward-image limits and tail-error estimates in
  both directions.

## References

* G. A. Elliott, *On the classification of C⋆-algebras of real rank zero*, J. Reine Angew. Math.
  443 (1993), 179–219, Theorem 2.1.
* M. Rørdam, *Classification of Nuclear, Simple C⋆-Algebras*, Encyclopaedia Math. Sci. 126, §2.3,
  Propositions 2.3.1 and 2.3.2.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace NonUnitalStarAlgHom

section NatLERec

variable {R : Type*} [Monoid R] {A : ℕ → Type*}
  [∀ n, NonUnitalNonAssocSemiring (A n)] [∀ n, DistribMulAction R (A n)] [∀ n, Star (A n)]

/-- Compose a sequence of one-step non-unital `⋆`-algebra homomorphisms
`α n : A n →⋆ₙₐ[R] A (n + 1)` into transition maps `A m →⋆ₙₐ[R] A n` for `m ≤ n`. -/
def natLERec (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) (m n : ℕ) (h : m ≤ n) : A m →⋆ₙₐ[R] A n :=
  Nat.leRecOn h (@fun k g ↦ (α k).comp g) (.id R (A m))

/-- Coercing `natLERec α m n h` to a function agrees with `Nat.leRecOn` on the underlying maps. -/
theorem coe_natLERec (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) (m n : ℕ) (h : m ≤ n) :
    ⇑(natLERec α m n h) = Nat.leRecOn h (@fun k ↦ ⇑(α k)) := by
  induction h with
  | refl =>
    ext x
    simp [natLERec, Nat.leRecOn_self]
  | @step k hmk ih =>
    ext x
    rw [natLERec, Nat.leRecOn_succ hmk, ← natLERec, Nat.leRecOn_succ hmk, comp_apply, ih]

@[simp]
theorem natLERec_self (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) (m : ℕ) :
    natLERec α m m le_rfl = .id R (A m) := by
  ext x
  simp [coe_natLERec, Nat.leRecOn_self]

@[simp]
theorem natLERec_succ (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) (m n : ℕ) (h : m ≤ n) :
    natLERec α m (n + 1) (Nat.le_succ_of_le h) = (α n).comp (natLERec α m n h) := by
  ext x
  simp [coe_natLERec, Nat.leRecOn_succ h]

/-- The one-step transition map `natLERec α n (n + 1)` equals `α n`. -/
theorem natLERec_add_one (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) (n : ℕ) :
    natLERec α n (n + 1) (Nat.le_succ n) = α n := by
  rw [natLERec_succ α n n le_rfl, natLERec_self, comp_id]

/-- Composing transition maps `natLERec α k m` and `natLERec α m n` gives `natLERec α k n`. -/
theorem natLERec_comp (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    (natLERec α m n hmn).comp (natLERec α k m hkm) = natLERec α k n (hkm.trans hmn) := by
  ext x
  simp [coe_natLERec, Nat.leRecOn_trans hkm hmn]

/-- Pointwise form of `NonUnitalStarAlgHom.natLERec_comp`. -/
theorem natLERec_apply_comp (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) (x : A k) :
    natLERec α m n hmn (natLERec α k m hkm x) = natLERec α k n (hkm.trans hmn) x :=
  DFunLike.congr_fun (natLERec_comp α hkm hmn) x

/-- Dependent-index congruence for applying a family of maps after `natLERec`. -/
theorem apply_natLERec_eq {B : Type*} {f : ∀ k, A k → B}
    (α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)) {m n₁ n₂ : ℕ}
    (h₁ : m ≤ n₁) (h₂ : m ≤ n₂) (hn : n₁ = n₂) (x : A m) :
    f n₁ (natLERec α m n₁ h₁ x) = f n₂ (natLERec α m n₂ h₂ x) := by
  subst hn
  rfl

@[simp]
theorem natLERec_id {B : Type*} [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
    (m n : ℕ) (h : m ≤ n) :
    natLERec (fun _ ↦ NonUnitalStarAlgHom.id R B) m n h = .id R B := by
  induction h with
  | refl => exact natLERec_self _ m
  | @step k hmk ih => rw [natLERec_succ _ m k hmk, ih, comp_id]

/-- A cocone `ι n : A n →⋆ₙₐ[R] B` compatible with one-step maps `α n` is compatible with all
iterated transition maps `natLERec α m n h`. -/
theorem comp_natLERec_eq {B : Type*} [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
    {α : ∀ n, A n →⋆ₙₐ[R] A (n + 1)} {ι : ∀ n, A n →⋆ₙₐ[R] B}
    (hι : ∀ n, (ι (n + 1)).comp (α n) = ι n) {m n : ℕ} (h : m ≤ n) :
    (ι n).comp (natLERec α m n h) = ι m := by
  induction h with
  | refl => rw [natLERec_self, comp_id]
  | @step k hmk ih => rw [natLERec_succ _ m k hmk, ← comp_assoc, hι, ih]

end NatLERec

end NonUnitalStarAlgHom

namespace TauCeti

/-- Predicate asserting that `C`, equipped with stage `⋆`-homomorphisms `ι n : A n →⋆ₙₐ[ℂ] C`,
is a C⋆-inductive limit of the sequential system `α n : A n →⋆ₙₐ[ℂ] A (n + 1)`: the maps `ι n` form
a cocone with dense union of ranges, and the seminorm `‖ι n x‖` is the limit of the stage norms
`‖α_{n, n+k} x‖` as `k → ∞`. Neither the `A n` nor `C` need be unital, and neither `α n` nor
`ι n` need be injective. -/
structure IsSequentialCStarLimit {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)]
    {C : Type*} [NonUnitalCStarAlgebra C]
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (ι : ∀ n, A n →⋆ₙₐ[ℂ] C) : Prop where
  /-- Cocone compatibility `(ι (n + 1)).comp (α n) = ι n` at every stage `n`. -/
  comp_eq (n : ℕ) : (ι (n + 1)).comp (α n) = ι n
  /-- The union of the stage images `Set.range (ι n)` is dense in `C`. -/
  dense_iUnion_range : Dense (⋃ n, Set.range (ι n))
  /-- For each `x : A n`, the forward stage norms `‖α_{n, n+k} x‖` converge to `‖ι n x‖`. -/
  tendsto_norm (n : ℕ) (x : A n) :
    Tendsto (fun k ↦ ‖NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x‖)
      atTop (𝓝 ‖ι n x‖)

namespace IsSequentialCStarLimit

section Basic

variable {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)]
  {C : Type*} [NonUnitalCStarAlgebra C]
  {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {ι : ∀ n, A n →⋆ₙₐ[ℂ] C}

/-- Compatibility of the cocone maps `ι` with multi-step transition maps `natLERec α m n`. -/
theorem comp_natLERec (h : IsSequentialCStarLimit α ι) {m n : ℕ} (hmn : m ≤ n) :
    (ι n).comp (NonUnitalStarAlgHom.natLERec α m n hmn) = ι m :=
  NonUnitalStarAlgHom.comp_natLERec_eq h.comp_eq hmn

/-- Pointwise compatibility `ι n (α_{m, n} x) = ι m x` for `m ≤ n`. -/
theorem comp_natLERec_apply (h : IsSequentialCStarLimit α ι) {m n : ℕ} (hmn : m ≤ n) (x : A m) :
    ι n (NonUnitalStarAlgHom.natLERec α m n hmn x) = ι m x :=
  DFunLike.congr_fun (h.comp_natLERec hmn) x

/-- The sequence of stage norms `k ↦ ‖α_{n, n+k} x‖` in any sequential C⋆-system is antitone. -/
theorem antitone_norm_natLERec (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (n : ℕ) (x : A n) :
    Antitone (fun k ↦ ‖NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x‖) := by
  refine antitone_nat_of_succ_le fun k ↦ ?_
  have hstep : NonUnitalStarAlgHom.natLERec α n (n + (k + 1)) (Nat.le_add_right n (k + 1)) x =
      α (n + k) (NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x) :=
    DFunLike.congr_fun (NonUnitalStarAlgHom.natLERec_succ α n (n + k) (Nat.le_add_right n k)) x
  rw [hstep]
  exact NonUnitalStarAlgHom.norm_apply_le (α (n + k)) _

/-- In a sequential C⋆-inductive limit, the norm in `C` of a stage element equals the infimum of
its forward stage norms. -/
theorem norm_eq_iInf (h : IsSequentialCStarLimit α ι) (n : ℕ) (x : A n) :
    ‖ι n x‖ = ⨅ k, ‖NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x‖ := by
  refine tendsto_nhds_unique (h.tendsto_norm n x) ?_
  exact tendsto_atTop_ciInf (antitone_norm_natLERec α n x) ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩

/-- Construct `IsSequentialCStarLimit` from the infimum formula
`‖ι n x‖ = ⨅ k, ‖α_{n, n+k} x‖`. -/
theorem of_norm_eq_iInf (hcomp : ∀ n, (ι (n + 1)).comp (α n) = ι n)
    (hdense : Dense (⋃ n, Set.range (ι n)))
    (hnorm : ∀ n (x : A n),
      ‖ι n x‖ = ⨅ k, ‖NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x‖) :
    IsSequentialCStarLimit α ι where
  comp_eq := hcomp
  dense_iUnion_range := hdense
  tendsto_norm n x := hnorm n x ▸
    tendsto_atTop_ciInf (antitone_norm_natLERec α n x) ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩

/-- Characterization of `IsSequentialCStarLimit` via `‖ι n x‖ = ⨅ k, ‖α_{n, n+k} x‖`. -/
theorem _root_.TauCeti.isSequentialCStarLimit_iff_norm_eq_iInf :
    IsSequentialCStarLimit α ι ↔
      (∀ n, (ι (n + 1)).comp (α n) = ι n) ∧
        Dense (⋃ n, Set.range (ι n)) ∧
        ∀ n (x : A n),
          ‖ι n x‖ = ⨅ k, ‖NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x‖ :=
  ⟨fun h ↦ ⟨h.comp_eq, h.dense_iUnion_range, h.norm_eq_iInf⟩,
    fun ⟨hc, hd, hn⟩ ↦ of_norm_eq_iInf hc hd hn⟩

/-- When every stage map `ι n : A n →⋆ₙₐ[ℂ] C` is injective (hence isometric), cocone
compatibility and density of `⋃ n, Set.range (ι n)` suffice for `IsSequentialCStarLimit`. -/
theorem of_injective (hcomp : ∀ n, (ι (n + 1)).comp (α n) = ι n)
    (hdense : Dense (⋃ n, Set.range (ι n))) (hinj : ∀ n, Function.Injective (ι n)) :
    IsSequentialCStarLimit α ι where
  comp_eq := hcomp
  dense_iUnion_range := hdense
  tendsto_norm n x := by
    have heq (k : ℕ) :
        ‖NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x‖ = ‖ι n x‖ := by
      rw [← NonUnitalStarAlgHom.norm_map (ι (n + k)) (hinj (n + k)),
        ← NonUnitalStarAlgHom.comp_apply,
        NonUnitalStarAlgHom.comp_natLERec_eq hcomp (Nat.le_add_right n k)]
    simp_rw [heq]
    exact tendsto_const_nhds

/-- The constant inductive system on a C⋆-algebra `B` has `B` itself as sequential limit. -/
theorem const (B : Type*) [NonUnitalCStarAlgebra B] :
    IsSequentialCStarLimit (fun _ ↦ NonUnitalStarAlgHom.id ℂ B)
      (fun _ ↦ NonUnitalStarAlgHom.id ℂ B) :=
  of_injective (fun _ ↦ rfl)
    (by
      convert dense_univ
      ext x
      simp)
    (fun _ ↦ Function.injective_id)

/-- Two continuous non-unital `⋆`-algebra homomorphisms out of `C` into a Hausdorff space that
agree on every stage `ι n x` are equal. -/
theorem ext_hom (h : IsSequentialCStarLimit α ι) {D : Type*} [TopologicalSpace D] [T2Space D]
    [NonUnitalNonAssocSemiring D] [DistribMulAction ℂ D] [Star D] {f g : C →⋆ₙₐ[ℂ] D}
    (hf : Continuous f) (hg : Continuous g) (heq : ∀ n x, f (ι n x) = g (ι n x)) : f = g := by
  have hdr : DenseRange (fun p : Σ n, A n ↦ ι p.1 p.2) := by
    rw [DenseRange, Set.range_sigma_eq_iUnion_range]
    exact h.dense_iUnion_range
  exact NonUnitalStarAlgHom.ext_of_denseRange hdr hf hg fun ⟨n, x⟩ ↦ heq n x

end Basic

section HomOfApprox

variable {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)]
  {C D : Type*} [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
  {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {ι : ∀ n, A n →⋆ₙₐ[ℂ] C}
  {F : ∀ n, Set (A n)} {d : ℕ → ℝ}

private theorem mapsTo_natLERec (hFα : ∀ n, Set.MapsTo (α n) (F n) (F (n + 1)))
    {m n : ℕ} (hmn : m ≤ n) :
    Set.MapsTo (NonUnitalStarAlgHom.natLERec α m n hmn) (F m) (F n) := by
  induction hmn with
  | refl =>
    intro x hx
    simpa using hx
  | @step k hmk ih =>
    intro x hx
    rw [NonUnitalStarAlgHom.natLERec_succ α m k hmk]
    exact hFα k (ih hx)

private theorem dist_approxSeq_succ_le (μ : ∀ n, A n →⋆ₙₐ[ℂ] D)
    (hFα : ∀ n, Set.MapsTo (α n) (F n) (F (n + 1)))
    (hμ : ∀ n, ∀ x ∈ F n, ‖μ (n + 1) (α n x) - μ n x‖ ≤ d n)
    {n : ℕ} {x : A n} (hx : x ∈ F n) (k : ℕ) :
    dist (μ (n + k) (NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x))
      (μ (n + (k + 1))
        (NonUnitalStarAlgHom.natLERec α n (n + (k + 1)) (Nat.le_add_right n (k + 1)) x)) ≤
      d (n + k) := by
  have hmem : NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x ∈ F (n + k) :=
    mapsTo_natLERec hFα (Nat.le_add_right n k) hx
  have hstep : NonUnitalStarAlgHom.natLERec α n (n + (k + 1)) (Nat.le_add_right n (k + 1)) x =
      α (n + k) (NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x) :=
    DFunLike.congr_fun (NonUnitalStarAlgHom.natLERec_succ α n (n + k) (Nat.le_add_right n k)) x
  rw [hstep, dist_eq_norm, norm_sub_rev]
  exact hμ (n + k) _ hmem

private theorem cauchySeq_approxSeq (μ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hd : Summable d)
    (hFα : ∀ n, Set.MapsTo (α n) (F n) (F (n + 1)))
    (hμ : ∀ n, ∀ x ∈ F n, ‖μ (n + 1) (α n x) - μ n x‖ ≤ d n)
    (hexh : ∀ n (x : A n) (ε : ℝ), 0 < ε →
      ∃ m, ∃ hnm : n ≤ m, ∃ x' ∈ F m, ‖NonUnitalStarAlgHom.natLERec α n m hnm x - x'‖ < ε)
    (n : ℕ) (x : A n) :
    CauchySeq (fun k ↦
      μ (n + k) (NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x)) := by
  have hcauchyF {m : ℕ} {y : A m} (hy : y ∈ F m) :
      CauchySeq (fun k ↦
        μ (m + k) (NonUnitalStarAlgHom.natLERec α m (m + k) (Nat.le_add_right m k) y)) :=
    cauchySeq_of_dist_le_of_summable (fun k ↦ d (m + k))
      (dist_approxSeq_succ_le μ hFα hμ hy) (hd.comp_injective (add_right_injective m))
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨m, hnm, x', hx', hxx'⟩ := hexh n x (ε / 3) (by positivity)
  obtain ⟨k₀, rfl⟩ := Nat.exists_eq_add_of_le hnm
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hcauchyF hx') (ε / 3) (by positivity)
  refine ⟨k₀ + N, fun k₁ hk₁ k₂ hk₂ ↦ ?_⟩
  obtain ⟨j₁, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right k₀ N) hk₁)
  obtain ⟨j₂, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right k₀ N) hk₂)
  have hclose (j : ℕ) :
      dist (μ (n + (k₀ + j))
          (NonUnitalStarAlgHom.natLERec α n (n + (k₀ + j)) (Nat.le_add_right n (k₀ + j)) x))
        (μ (n + k₀ + j)
          (NonUnitalStarAlgHom.natLERec α (n + k₀) (n + k₀ + j)
            (Nat.le_add_right (n + k₀) j) x')) < ε / 3 := by
    have hcomp :
        μ (n + (k₀ + j))
          (NonUnitalStarAlgHom.natLERec α n (n + (k₀ + j)) (Nat.le_add_right n (k₀ + j)) x) =
        μ (n + k₀ + j)
          (NonUnitalStarAlgHom.natLERec α (n + k₀) (n + k₀ + j) (Nat.le_add_right (n + k₀) j)
            (NonUnitalStarAlgHom.natLERec α n (n + k₀) hnm x)) := by
      rw [NonUnitalStarAlgHom.natLERec_apply_comp α hnm (Nat.le_add_right (n + k₀) j) x]
      exact NonUnitalStarAlgHom.apply_natLERec_eq (f := fun k ↦ ⇑(μ k)) α
        (Nat.le_add_right n (k₀ + j)) (hnm.trans (Nat.le_add_right (n + k₀) j)) (by omega) x
    rw [hcomp, dist_eq_norm, ← map_sub (μ (n + k₀ + j)), ← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le (μ (n + k₀ + j)) _).trans_lt <|
      (NonUnitalStarAlgHom.norm_apply_le _ _).trans_lt hxx'
  have hmid : dist
      (μ (n + k₀ + j₁)
        (NonUnitalStarAlgHom.natLERec α (n + k₀) (n + k₀ + j₁)
          (Nat.le_add_right (n + k₀) j₁) x'))
      (μ (n + k₀ + j₂)
        (NonUnitalStarAlgHom.natLERec α (n + k₀) (n + k₀ + j₂)
          (Nat.le_add_right (n + k₀) j₂) x')) < ε / 3 :=
    hN j₁ (by omega) j₂ (by omega)
  calc
    dist (μ (n + (k₀ + j₁))
        (NonUnitalStarAlgHom.natLERec α n (n + (k₀ + j₁)) (Nat.le_add_right n (k₀ + j₁)) x))
        (μ (n + (k₀ + j₂))
          (NonUnitalStarAlgHom.natLERec α n (n + (k₀ + j₂)) (Nat.le_add_right n (k₀ + j₂)) x))
      ≤ dist (μ (n + (k₀ + j₁))
          (NonUnitalStarAlgHom.natLERec α n (n + (k₀ + j₁)) (Nat.le_add_right n (k₀ + j₁)) x))
          (μ (n + k₀ + j₁)
            (NonUnitalStarAlgHom.natLERec α (n + k₀) (n + k₀ + j₁)
              (Nat.le_add_right (n + k₀) j₁) x')) +
        dist
          (μ (n + k₀ + j₁)
            (NonUnitalStarAlgHom.natLERec α (n + k₀) (n + k₀ + j₁)
              (Nat.le_add_right (n + k₀) j₁) x'))
          (μ (n + k₀ + j₂)
            (NonUnitalStarAlgHom.natLERec α (n + k₀) (n + k₀ + j₂)
              (Nat.le_add_right (n + k₀) j₂) x')) +
        dist
          (μ (n + k₀ + j₂)
            (NonUnitalStarAlgHom.natLERec α (n + k₀) (n + k₀ + j₂)
              (Nat.le_add_right (n + k₀) j₂) x'))
          (μ (n + (k₀ + j₂))
            (NonUnitalStarAlgHom.natLERec α n (n + (k₀ + j₂))
              (Nat.le_add_right n (k₀ + j₂)) x)) :=
      dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · exact hclose j₁
      · rw [dist_comm]
        exact hclose j₂
    _ = ε := by ring

private noncomputable def stageHomOfApprox (μ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hd : Summable d)
    (hFα : ∀ n, Set.MapsTo (α n) (F n) (F (n + 1)))
    (hμ : ∀ n, ∀ x ∈ F n, ‖μ (n + 1) (α n x) - μ n x‖ ≤ d n)
    (hexh : ∀ n (x : A n) (ε : ℝ), 0 < ε →
      ∃ m, ∃ hnm : n ≤ m, ∃ x' ∈ F m, ‖NonUnitalStarAlgHom.natLERec α n m hnm x - x'‖ < ε)
    (n : ℕ) : A n →⋆ₙₐ[ℂ] D :=
  NonUnitalStarAlgHom.ofTendsto
    (fun x ↦ limUnder atTop fun k ↦
      μ (n + k) (NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x))
    (fun k ↦ (μ (n + k)).comp (NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k)))
    fun x ↦ by
      simpa only [NonUnitalStarAlgHom.comp_apply] using
        (cauchySeq_approxSeq μ hd hFα hμ hexh n x).tendsto_limUnder

private theorem tendsto_stageHomOfApprox (μ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hd : Summable d)
    (hFα : ∀ n, Set.MapsTo (α n) (F n) (F (n + 1)))
    (hμ : ∀ n, ∀ x ∈ F n, ‖μ (n + 1) (α n x) - μ n x‖ ≤ d n)
    (hexh : ∀ n (x : A n) (ε : ℝ), 0 < ε →
      ∃ m, ∃ hnm : n ≤ m, ∃ x' ∈ F m, ‖NonUnitalStarAlgHom.natLERec α n m hnm x - x'‖ < ε)
    (n : ℕ) (x : A n) :
    Tendsto (fun k ↦
      μ (n + k) (NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x))
      atTop (𝓝 (stageHomOfApprox μ hd hFα hμ hexh n x)) := by
  dsimp only [stageHomOfApprox]
  rw [NonUnitalStarAlgHom.ofTendsto_apply]
  exact (cauchySeq_approxSeq μ hd hFα hμ hexh n x).tendsto_limUnder

private theorem stageHomOfApprox_comp_eq (μ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hd : Summable d)
    (hFα : ∀ n, Set.MapsTo (α n) (F n) (F (n + 1)))
    (hμ : ∀ n, ∀ x ∈ F n, ‖μ (n + 1) (α n x) - μ n x‖ ≤ d n)
    (hexh : ∀ n (x : A n) (ε : ℝ), 0 < ε →
      ∃ m, ∃ hnm : n ≤ m, ∃ x' ∈ F m, ‖NonUnitalStarAlgHom.natLERec α n m hnm x - x'‖ < ε)
    (n : ℕ) :
    (stageHomOfApprox μ hd hFα hμ hexh (n + 1)).comp (α n) =
      stageHomOfApprox μ hd hFα hμ hexh n := by
  ext x
  have hshift : Tendsto (fun k ↦
      μ (n + (k + 1))
        (NonUnitalStarAlgHom.natLERec α n (n + (k + 1)) (Nat.le_add_right n (k + 1)) x))
      atTop (𝓝 (stageHomOfApprox μ hd hFα hμ hexh n x)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_stageHomOfApprox μ hd hFα hμ hexh n x)
  have heq (k : ℕ) :
      μ (n + 1 + k)
        (NonUnitalStarAlgHom.natLERec α (n + 1) (n + 1 + k) (Nat.le_add_right (n + 1) k) (α n x)) =
      μ (n + (k + 1))
        (NonUnitalStarAlgHom.natLERec α n (n + (k + 1)) (Nat.le_add_right n (k + 1)) x) := by
    rw [← NonUnitalStarAlgHom.natLERec_add_one α n,
      NonUnitalStarAlgHom.natLERec_apply_comp α (Nat.le_succ n) (Nat.le_add_right (n + 1) k) x]
    exact NonUnitalStarAlgHom.apply_natLERec_eq (f := fun m ↦ ⇑(μ m)) α
      ((Nat.le_succ n).trans (Nat.le_add_right (n + 1) k)) (Nat.le_add_right n (k + 1))
      (by omega) x
  exact tendsto_nhds_unique
    (by simpa only [NonUnitalStarAlgHom.comp_apply, heq] using
      tendsto_stageHomOfApprox μ hd hFα hμ hexh (n + 1) (α n x))
    hshift

private theorem norm_stageHomOfApprox_le (hA : IsSequentialCStarLimit α ι)
    (μ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hd : Summable d)
    (hFα : ∀ n, Set.MapsTo (α n) (F n) (F (n + 1)))
    (hμ : ∀ n, ∀ x ∈ F n, ‖μ (n + 1) (α n x) - μ n x‖ ≤ d n)
    (hexh : ∀ n (x : A n) (ε : ℝ), 0 < ε →
      ∃ m, ∃ hnm : n ≤ m, ∃ x' ∈ F m, ‖NonUnitalStarAlgHom.natLERec α n m hnm x - x'‖ < ε)
    (n : ℕ) (x : A n) :
    ‖stageHomOfApprox μ hd hFα hμ hexh n x‖ ≤ ‖ι n x‖ :=
  le_of_tendsto_of_tendsto (tendsto_stageHomOfApprox μ hd hFα hμ hexh n x).norm
    (hA.tendsto_norm n x) <| Eventually.of_forall fun k ↦
      NonUnitalStarAlgHom.norm_apply_le (μ (n + k)) _

/-- Construct a limit non-unital `⋆`-algebra homomorphism `C →⋆ₙₐ[ℂ] D` out of a sequential
C⋆-inductive limit `(A, α, ι, C)` from an approximate cocone `μ n : A n →⋆ₙₐ[ℂ] D` with summable
discrepancies `‖μ (n + 1) (α n x) - μ n x‖ ≤ d n` on propagating subsets `F n` that approximate
every stage element at later stages (Rørdam, §2.3, Proposition 2.3.1). -/
noncomputable def homOfApprox (hA : IsSequentialCStarLimit α ι)
    (μ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hd : Summable d)
    (hFα : ∀ n, Set.MapsTo (α n) (F n) (F (n + 1)))
    (hμ : ∀ n, ∀ x ∈ F n, ‖μ (n + 1) (α n x) - μ n x‖ ≤ d n)
    (hexh : ∀ n (x : A n) (ε : ℝ), 0 < ε →
      ∃ m, ∃ hnm : n ≤ m, ∃ x' ∈ F m, ‖NonUnitalStarAlgHom.natLERec α n m hnm x - x'‖ < ε) :
    C →⋆ₙₐ[ℂ] D := by
  let L := stageHomOfApprox μ hd hFα hμ hexh
  have hLcomp := stageHomOfApprox_comp_eq μ hd hFα hμ hexh
  have hLnorm := norm_stageHomOfApprox_le hA μ hd hFα hμ hexh
  let K : ℕ → NonUnitalStarSubalgebra ℂ C := fun n ↦ (ι n).range
  have hKmono : Monotone K := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    change (ι n).range ≤ (ι (n + 1)).range
    rw [← hA.comp_eq n]
    exact NonUnitalStarAlgHom.range_comp_le_range (α n) (ι (n + 1))
  have hKdir : Directed (· ≤ ·) K := hKmono.directed_le
  have hL_eq_of_ι_eq : ∀ {i j : ℕ} {x : A i} {y : A j}, ι i x = ι j y → L i x = L j y := by
    intro i j x y hxy
    let N := max i j
    have hiN : i ≤ N := le_max_left i j
    have hjN : j ≤ N := le_max_right i j
    have hιN : ι N (NonUnitalStarAlgHom.natLERec α i N hiN x -
        NonUnitalStarAlgHom.natLERec α j N hjN y) = 0 := by
      rw [map_sub, hA.comp_natLERec_apply hiN, hA.comp_natLERec_apply hjN, hxy, sub_self]
    have hLN : L N (NonUnitalStarAlgHom.natLERec α i N hiN x -
        NonUnitalStarAlgHom.natLERec α j N hjN y) = 0 := by
      refine norm_le_zero_iff.mp ?_
      exact (hLnorm N _).trans (by rw [hιN, norm_zero])
    have hiL := DFunLike.congr_fun (NonUnitalStarAlgHom.comp_natLERec_eq hLcomp hiN) x
    have hjL := DFunLike.congr_fun (NonUnitalStarAlgHom.comp_natLERec_eq hLcomp hjN) y
    rw [map_sub, sub_eq_zero] at hLN
    exact hiL.symm.trans (hLN.trans hjL)
  let pre : ∀ {n : ℕ}, K n → A n := fun {n} z ↦ ((ι n).mem_range.mp z.2).choose
  have hpre : ∀ {n : ℕ} (z : K n), ι n (pre z) = z :=
    fun {n} z ↦ ((ι n).mem_range.mp z.2).choose_spec
  let f : ∀ n, K n →⋆ₙₐ[ℂ] D := fun n ↦
    { toFun := fun z ↦ L n (pre z)
      map_zero' := by
        have h0 : ι n (pre (0 : K n)) = ι n 0 := by
          rw [hpre, ZeroMemClass.coe_zero, map_zero]
        exact (hL_eq_of_ι_eq h0).trans (map_zero (L n))
      map_add' := fun z₁ z₂ ↦ by
        have h1 : ι n (pre (z₁ + z₂)) = ι n (pre z₁ + pre z₂) := by
          rw [hpre, map_add, hpre, hpre, AddMemClass.coe_add]
        exact (hL_eq_of_ι_eq h1).trans (map_add (L n) _ _)
      map_mul' := fun z₁ z₂ ↦ by
        have h1 : ι n (pre (z₁ * z₂)) = ι n (pre z₁ * pre z₂) := by
          rw [hpre, map_mul, hpre, hpre, MulMemClass.coe_mul]
        exact (hL_eq_of_ι_eq h1).trans (map_mul (L n) _ _)
      map_smul' := fun r z ↦ by
        have h1 : ι n (pre (r • z)) = ι n (r • pre z) := by
          rw [hpre, map_smul, hpre, SetLike.val_smul]
        simp only [MonoidHom.id_apply]
        exact (hL_eq_of_ι_eq h1).trans (map_smul (L n) r _)
      map_star' := fun z ↦ by
        have h1 : ι n (pre (star z)) = ι n (star (pre z)) := by
          rw [hpre, map_star, hpre, StarMemClass.coe_star]
        exact (hL_eq_of_ι_eq h1).trans (map_star (L n) _) }
  have hf_compat : ∀ (i j : ℕ) (h : K i ≤ K j),
      f i = (f j).comp (NonUnitalStarSubalgebra.inclusion h) := by
    intro i j h
    ext z
    exact hL_eq_of_ι_eq ((hpre z).trans (hpre (NonUnitalStarSubalgebra.inclusion h z)).symm)
  let S : NonUnitalStarSubalgebra ℂ C := ⨆ n, K n
  let fS : S →⋆ₙₐ[ℂ] D := NonUnitalStarSubalgebra.iSupLift K hKdir f hf_compat S rfl
  have hfS_norm : ∀ z : S, ‖fS z‖ ≤ 1 * ‖z‖ := by
    intro z
    have hz : (z : C) ∈ ⋃ n, (K n : Set C) := by
      rw [← NonUnitalStarSubalgebra.coe_iSup_of_directed hKdir]
      exact z.2
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    have hval : fS z = f n ⟨z, hn⟩ := NonUnitalStarSubalgebra.iSupLift_of_mem z hn
    rw [one_mul, hval]
    exact (hLnorm n _).trans_eq (congrArg norm (hpre ⟨z, hn⟩))
  have hfS_uc : UniformContinuous fS := AddMonoidHomClass.uniformContinuous_of_bound fS 1 hfS_norm
  have hS_dense : Dense (S : Set C) := by
    rw [NonUnitalStarSubalgebra.coe_iSup_of_directed hKdir]
    exact hA.dense_iUnion_range
  exact IsDenseInducing.extendNonUnitalStarAlgHom
    (i := NonUnitalStarSubalgebraClass.subtype S)
    (by rw [NonUnitalStarSubalgebraClass.coe_subtype]; exact ⟨rfl⟩)
    (by rw [NonUnitalStarSubalgebraClass.coe_subtype]; exact hS_dense.denseRange_val)
    hfS_uc

private theorem homOfApprox_ι_apply (hA : IsSequentialCStarLimit α ι)
    (μ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hd : Summable d)
    (hFα : ∀ n, Set.MapsTo (α n) (F n) (F (n + 1)))
    (hμ : ∀ n, ∀ x ∈ F n, ‖μ (n + 1) (α n x) - μ n x‖ ≤ d n)
    (hexh : ∀ n (x : A n) (ε : ℝ), 0 < ε →
      ∃ m, ∃ hnm : n ≤ m, ∃ x' ∈ F m, ‖NonUnitalStarAlgHom.natLERec α n m hnm x - x'‖ < ε)
    (n : ℕ) (x : A n) :
    hA.homOfApprox μ hd hFα hμ hexh (ι n x) = stageHomOfApprox μ hd hFα hμ hexh n x := by
  dsimp only [homOfApprox]
  let K : ℕ → NonUnitalStarSubalgebra ℂ C := fun m ↦ (ι m).range
  let S : NonUnitalStarSubalgebra ℂ C := ⨆ m, K m
  have hxK : ι n x ∈ K n := (ι n).mem_range_self x
  have hxS : ι n x ∈ S := le_iSup K n hxK
  change IsDenseInducing.extendNonUnitalStarAlgHom _ _ _
      (NonUnitalStarSubalgebraClass.subtype S ⟨ι n x, hxS⟩) = _
  rw [IsDenseInducing.extendNonUnitalStarAlgHom_apply,
    NonUnitalStarSubalgebra.iSupLift_mk (K := K) ⟨ι n x, hxK⟩ hxS]
  simp only [NonUnitalStarAlgHom.coe_mk]
  have hchoose : ι n (((ι n).mem_range.mp hxK).choose) = ι n x :=
    ((ι n).mem_range.mp hxK).choose_spec
  have hsub : ι n (((ι n).mem_range.mp hxK).choose - x) = 0 := by
    rw [map_sub, hchoose, sub_self]
  refine sub_eq_zero.mp (norm_le_zero_iff.mp ?_)
  rw [← map_sub]
  exact (norm_stageHomOfApprox_le hA μ hd hFα hμ hexh n _).trans (by rw [hsub, norm_zero])

/-- Forward-image convergence for `IsSequentialCStarLimit.homOfApprox`: for every stage `n` and
`x : A n`, `μ (n + k) (α_{n, n+k} x)` converges to `homOfApprox (ι n x)` as `k → ∞`. -/
theorem tendsto_homOfApprox (hA : IsSequentialCStarLimit α ι)
    (μ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hd : Summable d)
    (hFα : ∀ n, Set.MapsTo (α n) (F n) (F (n + 1)))
    (hμ : ∀ n, ∀ x ∈ F n, ‖μ (n + 1) (α n x) - μ n x‖ ≤ d n)
    (hexh : ∀ n (x : A n) (ε : ℝ), 0 < ε →
      ∃ m, ∃ hnm : n ≤ m, ∃ x' ∈ F m, ‖NonUnitalStarAlgHom.natLERec α n m hnm x - x'‖ < ε)
    (n : ℕ) (x : A n) :
    Tendsto (fun k ↦
      μ (n + k) (NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x))
      atTop (𝓝 (hA.homOfApprox μ hd hFα hμ hexh (ι n x))) := by
  rw [homOfApprox_ι_apply]
  exact tendsto_stageHomOfApprox μ hd hFα hμ hexh n x

/-- Tail-error estimate for `IsSequentialCStarLimit.homOfApprox` on the propagating set `F n`. -/
theorem norm_homOfApprox_sub_le (hA : IsSequentialCStarLimit α ι)
    (μ : ∀ n, A n →⋆ₙₐ[ℂ] D) (hd : Summable d)
    (hFα : ∀ n, Set.MapsTo (α n) (F n) (F (n + 1)))
    (hμ : ∀ n, ∀ x ∈ F n, ‖μ (n + 1) (α n x) - μ n x‖ ≤ d n)
    (hexh : ∀ n (x : A n) (ε : ℝ), 0 < ε →
      ∃ m, ∃ hnm : n ≤ m, ∃ x' ∈ F m, ‖NonUnitalStarAlgHom.natLERec α n m hnm x - x'‖ < ε)
    {n : ℕ} {x : A n} (hx : x ∈ F n) :
    ‖hA.homOfApprox μ hd hFα hμ hexh (ι n x) - μ n x‖ ≤ ∑' k, d (n + k) := by
  have hdist := dist_le_tsum_of_dist_le_of_tendsto₀ (fun k ↦ d (n + k))
    (dist_approxSeq_succ_le μ hFα hμ hx) (hd.comp_injective (add_right_injective n))
    (hA.tendsto_homOfApprox μ hd hFα hμ hexh n x)
  simpa only [Nat.add_zero, NonUnitalStarAlgHom.natLERec_self, NonUnitalStarAlgHom.coe_id, id_eq,
    dist_eq_norm, norm_sub_rev] using hdist

end HomOfApprox

end IsSequentialCStarLimit

/-- An analytic approximate intertwining between two sequential systems of possibly nonunital
complex C⋆-algebras `α n : A n →⋆ₙₐ[ℂ] A (n + 1)` and `β n : B n →⋆ₙₐ[ℂ] B (n + 1)` along
`φ n : A n →⋆ₙₐ[ℂ] B (n + 1)` and `ψ n : B n →⋆ₙₐ[ℂ] A n` (Rørdam, §2.3, Proposition 2.3.2):
subsets `F n ⊆ A n` and `G n ⊆ B n` propagate under all four maps, the triangles commute on `F n`
and `G n` up to summable errors `δA n` and `δB n`, and every element of every stage can be
approximated in a later `F m` or `G m`. -/
structure ApproximateIntertwining {A : ℕ → Type*} {B : ℕ → Type*}
    [∀ n, NonUnitalCStarAlgebra (A n)] [∀ n, NonUnitalCStarAlgebra (B n)]
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ : ∀ n, B n →⋆ₙₐ[ℂ] A n) where
  /-- Propagating subsets `F n ⊆ A n` on which the `A`-triangles approximately commute. -/
  F : ∀ n, Set (A n)
  /-- Propagating subsets `G n ⊆ B n` on which the `B`-triangles approximately commute. -/
  G : ∀ n, Set (B n)
  /-- Stagewise error bounds for `‖ψ (n + 1) (φ n x) - α n x‖` on `F n`. -/
  δA : ℕ → ℝ
  /-- Stagewise error bounds for `‖φ n (ψ n y) - β n y‖` on `G n`. -/
  δB : ℕ → ℝ
  /-- Summability of the `A`-triangle error sequence `δA`. -/
  summable_δA : Summable δA
  /-- Summability of the `B`-triangle error sequence `δB`. -/
  summable_δB : Summable δB
  /-- Approximate commutativity `‖ψ (n + 1) (φ n x) - α n x‖ ≤ δA n` on `F n`. -/
  norm_psi_phi_sub_le (n : ℕ) ⦃x : A n⦄ (hx : x ∈ F n) :
    ‖ψ (n + 1) (φ n x) - α n x‖ ≤ δA n
  /-- Approximate commutativity `‖φ n (ψ n y) - β n y‖ ≤ δB n` on `G n`. -/
  norm_phi_psi_sub_le (n : ℕ) ⦃y : B n⦄ (hy : y ∈ G n) :
    ‖φ n (ψ n y) - β n y‖ ≤ δB n
  /-- Propagation of `F n` into `F (n + 1)` under `α n`. -/
  mapsTo_alpha (n : ℕ) : Set.MapsTo (α n) (F n) (F (n + 1))
  /-- Propagation of `G n` into `G (n + 1)` under `β n`. -/
  mapsTo_beta (n : ℕ) : Set.MapsTo (β n) (G n) (G (n + 1))
  /-- Propagation of `F n` into `G (n + 1)` under `φ n`. -/
  mapsTo_phi (n : ℕ) : Set.MapsTo (φ n) (F n) (G (n + 1))
  /-- Propagation of `G n` into `F n` under `ψ n`. -/
  mapsTo_psi (n : ℕ) : Set.MapsTo (ψ n) (G n) (F n)
  /-- Every stage element `x : A n` can be approximated at a later stage `m ≥ n` by `F m`. -/
  approx_A (n : ℕ) (x : A n) {ε : ℝ} (hε : 0 < ε) :
    ∃ m, ∃ hnm : n ≤ m, ∃ x' ∈ F m, ‖NonUnitalStarAlgHom.natLERec α n m hnm x - x'‖ < ε
  /-- Every stage element `y : B n` can be approximated at a later stage `m ≥ n` by `G m`. -/
  approx_B (n : ℕ) (y : B n) {ε : ℝ} (hε : 0 < ε) :
    ∃ m, ∃ hnm : n ≤ m, ∃ y' ∈ G m, ‖NonUnitalStarAlgHom.natLERec β n m hnm y - y'‖ < ε

namespace ApproximateIntertwining

variable {A : ℕ → Type*} {B : ℕ → Type*}
  [∀ n, NonUnitalCStarAlgebra (A n)] [∀ n, NonUnitalCStarAlgebra (B n)]
  {C : Type*} {D : Type*} [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
  {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1)}
  {φ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)} {ψ : ∀ n, B n →⋆ₙₐ[ℂ] A n}
  {ιA : ∀ n, A n →⋆ₙₐ[ℂ] C} {ιB : ∀ n, B n →⋆ₙₐ[ℂ] D}

private theorem summable_stepErrA (H : ApproximateIntertwining α β φ ψ) :
    Summable (fun n ↦ H.δA n + H.δB (n + 1)) :=
  H.summable_δA.add (H.summable_δB.comp_injective (add_left_injective 1))

private theorem summable_stepErrB (H : ApproximateIntertwining α β φ ψ) :
    Summable (fun n ↦ H.δB n + H.δA n) :=
  H.summable_δB.add H.summable_δA

private theorem norm_stepA_le (H : ApproximateIntertwining α β φ ψ)
    (hB : IsSequentialCStarLimit β ιB) (n : ℕ) {x : A n} (hx : x ∈ H.F n) :
    ‖((ιB (n + 2)).comp (φ (n + 1))) (α n x) - ((ιB (n + 1)).comp (φ n)) x‖ ≤
      H.δA n + H.δB (n + 1) := by
  simp only [NonUnitalStarAlgHom.comp_apply]
  rw [← DFunLike.congr_fun (hB.comp_eq (n + 1)) (φ n x), NonUnitalStarAlgHom.comp_apply,
    ← map_sub]
  refine (NonUnitalStarAlgHom.norm_apply_le (ιB (n + 2)) _).trans ?_
  have hsplit : φ (n + 1) (α n x) - β (n + 1) (φ n x) =
      φ (n + 1) (α n x - ψ (n + 1) (φ n x)) +
        (φ (n + 1) (ψ (n + 1) (φ n x)) - β (n + 1) (φ n x)) := by
    rw [map_sub, sub_add_sub_cancel]
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (NonUnitalStarAlgHom.norm_apply_le (φ (n + 1)) _).trans
      (norm_sub_rev (ψ (n + 1) (φ n x)) (α n x) ▸ H.norm_psi_phi_sub_le n hx)
  · exact H.norm_phi_psi_sub_le (n + 1) (H.mapsTo_phi n hx)

private theorem norm_stepB_le (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (n : ℕ) {y : B n} (hy : y ∈ H.G n) :
    ‖((ιA (n + 1)).comp (ψ (n + 1))) (β n y) - ((ιA n).comp (ψ n)) y‖ ≤
      H.δB n + H.δA n := by
  simp only [NonUnitalStarAlgHom.comp_apply]
  rw [← DFunLike.congr_fun (hA.comp_eq n) (ψ n y), NonUnitalStarAlgHom.comp_apply, ← map_sub]
  refine (NonUnitalStarAlgHom.norm_apply_le (ιA (n + 1)) _).trans ?_
  have hsplit : ψ (n + 1) (β n y) - α n (ψ n y) =
      ψ (n + 1) (β n y - φ n (ψ n y)) + (ψ (n + 1) (φ n (ψ n y)) - α n (ψ n y)) := by
    rw [map_sub, sub_add_sub_cancel]
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (NonUnitalStarAlgHom.norm_apply_le (ψ (n + 1)) _).trans
      (norm_sub_rev (φ n (ψ n y)) (β n y) ▸ H.norm_phi_psi_sub_le n hy)
  · exact H.norm_psi_phi_sub_le n (H.mapsTo_psi n hy)

/-- The forward limit `⋆`-homomorphism `C →⋆ₙₐ[ℂ] D` induced by an approximate intertwining. -/
noncomputable def toHom (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB) : C →⋆ₙₐ[ℂ] D :=
  hA.homOfApprox (fun n ↦ (ιB (n + 1)).comp (φ n)) H.summable_stepErrA H.mapsTo_alpha
    (fun n _ hx ↦ H.norm_stepA_le hB n hx) (fun n x _ hε ↦ H.approx_A n x hε)

/-- The backward limit `⋆`-homomorphism `D →⋆ₙₐ[ℂ] C` induced by an approximate intertwining. -/
noncomputable def invHom (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB) : D →⋆ₙₐ[ℂ] C :=
  hB.homOfApprox (fun n ↦ (ιA n).comp (ψ n)) H.summable_stepErrB H.mapsTo_beta
    (fun n _ hy ↦ H.norm_stepB_le hA n hy) (fun n y _ hε ↦ H.approx_B n y hε)

/-- Forward-image convergence for `ApproximateIntertwining.toHom`. -/
theorem tendsto_toHom_apply (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB) (n : ℕ) (x : A n) :
    Tendsto (fun k ↦
      ιB (n + k + 1) (φ (n + k)
        (NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x)))
      atTop (𝓝 (H.toHom hA hB (ιA n x))) := by
  simpa only [toHom, NonUnitalStarAlgHom.comp_apply] using
    hA.tendsto_homOfApprox (fun m ↦ (ιB (m + 1)).comp (φ m)) H.summable_stepErrA H.mapsTo_alpha
      (fun m _ hx ↦ H.norm_stepA_le hB m hx) (fun m z _ hε ↦ H.approx_A m z hε) n x

/-- Backward-image convergence for `ApproximateIntertwining.invHom`. -/
theorem tendsto_invHom_apply (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB) (n : ℕ) (y : B n) :
    Tendsto (fun k ↦
      ιA (n + k) (ψ (n + k)
        (NonUnitalStarAlgHom.natLERec β n (n + k) (Nat.le_add_right n k) y)))
      atTop (𝓝 (H.invHom hA hB (ιB n y))) := by
  simpa only [invHom, NonUnitalStarAlgHom.comp_apply] using
    hB.tendsto_homOfApprox (fun m ↦ (ιA m).comp (ψ m)) H.summable_stepErrB H.mapsTo_beta
      (fun m _ hy ↦ H.norm_stepB_le hA m hy) (fun m w _ hε ↦ H.approx_B m w hε) n y

/-- Tail-error estimate for `ApproximateIntertwining.toHom` on `H.F n`. -/
theorem norm_toHom_apply_sub_le (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB)
    {n : ℕ} {x : A n} (hx : x ∈ H.F n) :
    ‖H.toHom hA hB (ιA n x) - ιB (n + 1) (φ n x)‖ ≤
      ∑' k, (H.δA (n + k) + H.δB (n + k + 1)) := by
  simpa only [toHom, NonUnitalStarAlgHom.comp_apply] using
    hA.norm_homOfApprox_sub_le (fun m ↦ (ιB (m + 1)).comp (φ m)) H.summable_stepErrA H.mapsTo_alpha
      (fun m _ hz ↦ H.norm_stepA_le hB m hz) (fun m z _ hε ↦ H.approx_A m z hε) hx

/-- Tail-error estimate for `ApproximateIntertwining.invHom` on `H.G n`. -/
theorem norm_invHom_apply_sub_le (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB)
    {n : ℕ} {y : B n} (hy : y ∈ H.G n) :
    ‖H.invHom hA hB (ιB n y) - ιA n (ψ n y)‖ ≤
      ∑' k, (H.δB (n + k) + H.δA (n + k)) := by
  simpa only [invHom, NonUnitalStarAlgHom.comp_apply] using
    hB.norm_homOfApprox_sub_le (fun m ↦ (ιA m).comp (ψ m)) H.summable_stepErrB H.mapsTo_beta
      (fun m _ hw ↦ H.norm_stepB_le hA m hw) (fun m w _ hε ↦ H.approx_B m w hε) hy

/-- The backward and forward limit homomorphisms of an approximate intertwining satisfy
`(H.invHom hA hB).comp (H.toHom hA hB) = .id ℂ C`. -/
theorem invHom_comp_toHom (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB) :
    (H.invHom hA hB).comp (H.toHom hA hB) = .id ℂ C := by
  have honF {m : ℕ} {x : A m} (hx : x ∈ H.F m) :
      H.invHom hA hB (H.toHom hA hB (ιA m x)) = ιA m x := by
    let xk := fun k ↦ NonUnitalStarAlgHom.natLERec α m (m + k) (Nat.le_add_right m k) x
    have ht1 : Tendsto (fun k ↦ H.invHom hA hB (ιB (m + k + 1) (φ (m + k) (xk k))))
        atTop (𝓝 (H.invHom hA hB (H.toHom hA hB (ιA m x)))) :=
      (map_continuous (H.invHom hA hB)).continuousAt.tendsto.comp
        (H.tendsto_toHom_apply hA hB m x)
    have htail : Tendsto (fun k ↦
        H.δA (m + k) + ∑' j, (H.δB (m + k + 1 + j) + H.δA (m + k + 1 + j)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun k ↦ H.δA (m + k)) atTop (𝓝 0) :=
        (H.summable_δA.comp_injective (add_right_injective m)).tendsto_atTop_zero
      have h2 : Tendsto (fun k ↦ ∑' j, (H.δB (j + (k + (m + 1))) + H.δA (j + (k + (m + 1)))))
          atTop (𝓝 0) :=
        (_root_.tendsto_sum_nat_add (fun i ↦ H.δB i + H.δA i)).comp
          (tendsto_add_atTop_nat (m + 1))
      have h2' : (fun k ↦ ∑' j, (H.δB (m + k + 1 + j) + H.δA (m + k + 1 + j))) =
          fun k ↦ ∑' j, (H.δB (j + (k + (m + 1))) + H.δA (j + (k + (m + 1)))) := by
        ext k
        congr 1 with j
        have hidx : m + k + 1 + j = j + (k + (m + 1)) := by omega
        rw [hidx]
      rw [← h2'] at h2
      simpa only [add_zero] using h1.add h2
    refine tendsto_nhds_unique ht1 ?_
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm (fun k ↦ ?_) htail
    have hxkF : xk k ∈ H.F (m + k) :=
      IsSequentialCStarLimit.mapsTo_natLERec H.mapsTo_alpha (Nat.le_add_right m k) hx
    have hφG : φ (m + k) (xk k) ∈ H.G (m + k + 1) := H.mapsTo_phi (m + k) hxkF
    have hb1 := H.norm_invHom_apply_sub_le hA hB hφG
    have hιeq : ιA m x = ιA (m + k + 1) (α (m + k) (xk k)) := by
      have hstep : NonUnitalStarAlgHom.natLERec α m (m + k + 1)
          (Nat.le_succ_of_le (Nat.le_add_right m k)) x = α (m + k) (xk k) :=
        DFunLike.congr_fun
          (NonUnitalStarAlgHom.natLERec_succ α m (m + k) (Nat.le_add_right m k)) x
      rw [← hA.comp_natLERec_apply (Nat.le_succ_of_le (Nat.le_add_right m k)) x, hstep]
    have hb2 : ‖ιA (m + k + 1) (ψ (m + k + 1) (φ (m + k) (xk k))) - ιA m x‖ ≤ H.δA (m + k) := by
      rw [hιeq, ← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le (ιA (m + k + 1)) _).trans
        (H.norm_psi_phi_sub_le (m + k) hxkF)
    calc
      ‖H.invHom hA hB (ιB (m + k + 1) (φ (m + k) (xk k))) - ιA m x‖
        ≤ ‖H.invHom hA hB (ιB (m + k + 1) (φ (m + k) (xk k))) -
            ιA (m + k + 1) (ψ (m + k + 1) (φ (m + k) (xk k)))‖ +
          ‖ιA (m + k + 1) (ψ (m + k + 1) (φ (m + k) (xk k))) - ιA m x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (∑' j, (H.δB (m + k + 1 + j) + H.δA (m + k + 1 + j))) + H.δA (m + k) :=
        add_le_add hb1 hb2
      _ = H.δA (m + k) + ∑' j, (H.δB (m + k + 1 + j) + H.δA (m + k + 1 + j)) := add_comm _ _
  refine hA.ext_hom (map_continuous _) (map_continuous _) fun n x ↦ ?_
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_id, id_eq]
  apply sub_eq_zero.mp
  apply norm_le_zero_iff.mp
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨m, hnm, x', hx', hxx'⟩ := H.approx_A n x (half_pos hε)
  have hdiff : ‖ιA n x - ιA m x'‖ < ε / 2 := by
    rw [← hA.comp_natLERec_apply hnm x, ← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le (ιA m) _).trans_lt hxx'
  have heq' : H.invHom hA hB (H.toHom hA hB (ιA n x)) - ιA n x =
      (H.invHom hA hB).comp (H.toHom hA hB) (ιA n x - ιA m x') - (ιA n x - ιA m x') := by
    simp only [NonUnitalStarAlgHom.comp_apply, map_sub, honF hx']
    abel
  rw [zero_add, heq']
  calc
    ‖(H.invHom hA hB).comp (H.toHom hA hB) (ιA n x - ιA m x') - (ιA n x - ιA m x')‖
      ≤ ‖(H.invHom hA hB).comp (H.toHom hA hB) (ιA n x - ιA m x')‖ + ‖ιA n x - ιA m x'‖ :=
      norm_sub_le _ _
    _ ≤ ‖ιA n x - ιA m x'‖ + ‖ιA n x - ιA m x'‖ :=
      add_le_add (NonUnitalStarAlgHom.norm_apply_le _ _) le_rfl
    _ ≤ ε / 2 + ε / 2 := add_le_add hdiff.le hdiff.le
    _ = ε := by ring

/-- The forward and backward limit homomorphisms of an approximate intertwining satisfy
`(H.toHom hA hB).comp (H.invHom hA hB) = .id ℂ D`. -/
theorem toHom_comp_invHom (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB) :
    (H.toHom hA hB).comp (H.invHom hA hB) = .id ℂ D := by
  have honG {m : ℕ} {y : B m} (hy : y ∈ H.G m) :
      H.toHom hA hB (H.invHom hA hB (ιB m y)) = ιB m y := by
    let yk := fun k ↦ NonUnitalStarAlgHom.natLERec β m (m + k) (Nat.le_add_right m k) y
    have ht1 : Tendsto (fun k ↦ H.toHom hA hB (ιA (m + k) (ψ (m + k) (yk k))))
        atTop (𝓝 (H.toHom hA hB (H.invHom hA hB (ιB m y)))) :=
      (map_continuous (H.toHom hA hB)).continuousAt.tendsto.comp
        (H.tendsto_invHom_apply hA hB m y)
    have htail : Tendsto (fun k ↦
        H.δB (m + k) + ∑' j, (H.δA (m + k + j) + H.δB (m + k + j + 1)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun k ↦ H.δB (m + k)) atTop (𝓝 0) :=
        (H.summable_δB.comp_injective (add_right_injective m)).tendsto_atTop_zero
      have h2 : Tendsto (fun k ↦ ∑' j, (H.δA (j + (k + m)) + H.δB (j + (k + m) + 1)))
          atTop (𝓝 0) :=
        (_root_.tendsto_sum_nat_add (fun i ↦ H.δA i + H.δB (i + 1))).comp
          (tendsto_add_atTop_nat m)
      have h2' : (fun k ↦ ∑' j, (H.δA (m + k + j) + H.δB (m + k + j + 1))) =
          fun k ↦ ∑' j, (H.δA (j + (k + m)) + H.δB (j + (k + m) + 1)) := by
        ext k
        congr 1 with j
        have hidx : m + k + j = j + (k + m) := by omega
        rw [hidx]
      rw [← h2'] at h2
      simpa only [add_zero] using h1.add h2
    refine tendsto_nhds_unique ht1 ?_
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm (fun k ↦ ?_) htail
    have hykG : yk k ∈ H.G (m + k) :=
      IsSequentialCStarLimit.mapsTo_natLERec H.mapsTo_beta (Nat.le_add_right m k) hy
    have hψF : ψ (m + k) (yk k) ∈ H.F (m + k) := H.mapsTo_psi (m + k) hykG
    have hb1 := H.norm_toHom_apply_sub_le hA hB hψF
    have hιeq : ιB m y = ιB (m + k + 1) (β (m + k) (yk k)) := by
      have hstep : NonUnitalStarAlgHom.natLERec β m (m + k + 1)
          (Nat.le_succ_of_le (Nat.le_add_right m k)) y = β (m + k) (yk k) :=
        DFunLike.congr_fun
          (NonUnitalStarAlgHom.natLERec_succ β m (m + k) (Nat.le_add_right m k)) y
      rw [← hB.comp_natLERec_apply (Nat.le_succ_of_le (Nat.le_add_right m k)) y, hstep]
    have hb2 : ‖ιB (m + k + 1) (φ (m + k) (ψ (m + k) (yk k))) - ιB m y‖ ≤ H.δB (m + k) := by
      rw [hιeq, ← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le (ιB (m + k + 1)) _).trans
        (H.norm_phi_psi_sub_le (m + k) hykG)
    calc
      ‖H.toHom hA hB (ιA (m + k) (ψ (m + k) (yk k))) - ιB m y‖
        ≤ ‖H.toHom hA hB (ιA (m + k) (ψ (m + k) (yk k))) -
            ιB (m + k + 1) (φ (m + k) (ψ (m + k) (yk k)))‖ +
          ‖ιB (m + k + 1) (φ (m + k) (ψ (m + k) (yk k))) - ιB m y‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (∑' j, (H.δA (m + k + j) + H.δB (m + k + j + 1))) + H.δB (m + k) :=
        add_le_add hb1 hb2
      _ = H.δB (m + k) + ∑' j, (H.δA (m + k + j) + H.δB (m + k + j + 1)) := add_comm _ _
  refine hB.ext_hom (map_continuous _) (map_continuous _) fun n y ↦ ?_
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_id, id_eq]
  apply sub_eq_zero.mp
  apply norm_le_zero_iff.mp
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨m, hnm, y', hy', hyy'⟩ := H.approx_B n y (half_pos hε)
  have hdiff : ‖ιB n y - ιB m y'‖ < ε / 2 := by
    rw [← hB.comp_natLERec_apply hnm y, ← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le (ιB m) _).trans_lt hyy'
  have heq' : H.toHom hA hB (H.invHom hA hB (ιB n y)) - ιB n y =
      (H.toHom hA hB).comp (H.invHom hA hB) (ιB n y - ιB m y') - (ιB n y - ιB m y') := by
    simp only [NonUnitalStarAlgHom.comp_apply, map_sub, honG hy']
    abel
  rw [zero_add, heq']
  calc
    ‖(H.toHom hA hB).comp (H.invHom hA hB) (ιB n y - ιB m y') - (ιB n y - ιB m y')‖
      ≤ ‖(H.toHom hA hB).comp (H.invHom hA hB) (ιB n y - ιB m y')‖ + ‖ιB n y - ιB m y'‖ :=
      norm_sub_le _ _
    _ ≤ ‖ιB n y - ιB m y'‖ + ‖ιB n y - ιB m y'‖ :=
      add_le_add (NonUnitalStarAlgHom.norm_apply_le _ _) le_rfl
    _ ≤ ε / 2 + ε / 2 := add_le_add hdiff.le hdiff.le
    _ = ε := by ring

/-- **Elliott's sequential approximate intertwining theorem** (Rørdam, §2.3, Proposition 2.3.2):
an approximate intertwining between sequential C⋆-inductive systems `(A, α)` and `(B, β)` induces
a `⋆`-algebra isomorphism `C ≃⋆ₐ[ℂ] D` between their C⋆-inductive limits. -/
noncomputable def equiv (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB) : C ≃⋆ₐ[ℂ] D :=
  StarAlgEquiv.ofNonUnitalStarAlgHom (H.toHom hA hB) (H.invHom hA hB)
    (H.invHom_comp_toHom hA hB) (H.toHom_comp_invHom hA hB)

@[simp]
theorem toNonUnitalStarAlgHom_equiv (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB) :
    (H.equiv hA hB).toNonUnitalStarAlgHom = H.toHom hA hB :=
  (rfl)

@[simp]
theorem toNonUnitalStarAlgHom_equiv_symm (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB) :
    (H.equiv hA hB).symm.toNonUnitalStarAlgHom = H.invHom hA hB :=
  (rfl)

/-- Forward-image convergence for the limit `⋆`-isomorphism `ApproximateIntertwining.equiv`. -/
theorem tendsto_equiv_apply (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB) (n : ℕ) (x : A n) :
    Tendsto (fun k ↦
      ιB (n + k + 1) (φ (n + k)
        (NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x)))
      atTop (𝓝 (H.equiv hA hB (ιA n x))) :=
  H.tendsto_toHom_apply hA hB n x

/-- Backward-image convergence for `(H.equiv hA hB).symm`. -/
theorem tendsto_equiv_symm_apply (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB) (n : ℕ) (y : B n) :
    Tendsto (fun k ↦
      ιA (n + k) (ψ (n + k)
        (NonUnitalStarAlgHom.natLERec β n (n + k) (Nat.le_add_right n k) y)))
      atTop (𝓝 ((H.equiv hA hB).symm (ιB n y))) :=
  H.tendsto_invHom_apply hA hB n y

/-- Tail-error estimate for `ApproximateIntertwining.equiv` on `H.F n`. -/
theorem norm_equiv_apply_sub_le (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB)
    {n : ℕ} {x : A n} (hx : x ∈ H.F n) :
    ‖H.equiv hA hB (ιA n x) - ιB (n + 1) (φ n x)‖ ≤
      ∑' k, (H.δA (n + k) + H.δB (n + k + 1)) :=
  H.norm_toHom_apply_sub_le hA hB hx

/-- Tail-error estimate for `(H.equiv hA hB).symm` on `H.G n`. -/
theorem norm_equiv_symm_apply_sub_le (H : ApproximateIntertwining α β φ ψ)
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB)
    {n : ℕ} {y : B n} (hy : y ∈ H.G n) :
    ‖(H.equiv hA hB).symm (ιB n y) - ιA n (ψ n y)‖ ≤
      ∑' k, (H.δB (n + k) + H.δA (n + k)) :=
  H.norm_invHom_apply_sub_le hA hB hy

end ApproximateIntertwining

end TauCeti
