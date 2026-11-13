/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateIntertwining.Basic
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Sequential

/-!
# Unitary approximate intertwining and Elliott's theorem

When the triangles of a sequential back-and-forth diagram between separable unital C⋆-algebras
commute up to `TauCeti.ApproximatelyUnitarilyEquivalent`, inductive unitary conjugation produces a
genuine `TauCeti.ApproximateIntertwining` with geometric error bounds `(1 / 2) ^ n`. Combining this
with `TauCeti.ApproximateIntertwining.equiv` yields a `⋆`-isomorphism between the sequential
C⋆-inductive limits, and specializing to constant inductive systems yields Elliott's two-algebra
approximate intertwining theorem (`TauCeti.elliott_intertwining`).

## Main results

* `TauCeti.ApproximateIntertwining.exists_of_approximatelyUnitarilyEquivalent`: conjugates an
  approximately unitarily commuting sequential diagram of separable unital C⋆-algebras into an
  `ApproximateIntertwining`.
* `TauCeti.IsSequentialCStarLimit.exists_starAlgEquiv_of_approximatelyUnitarilyEquivalent`:
  deduces a `⋆`-isomorphism `C ≃⋆ₐ[ℂ] D` between the sequential C⋆-inductive limits together with
  pointwise convergence of the unitarily conjugated stage maps in both directions.
* `TauCeti.elliott_intertwining`: if `φ : A →⋆ₙₐ[ℂ] B` and `ψ : B →⋆ₙₐ[ℂ] A` between separable
  unital C⋆-algebras satisfy `ψ ∘ φ ≈_u id_A` and `φ ∘ ψ ≈_u id_B`, then there is a `⋆`-isomorphism
  `θ : A ≃⋆ₐ[ℂ] B` with `θ ≈_u φ` (and hence `θ.symm ≈_u ψ` via
  `TauCeti.ApproximatelyUnitarilyEquivalent.symm_of_comp_id`).

## References

* G. A. Elliott, *On the classification of C⋆-algebras of real rank zero*, J. Reine Angew. Math.
  443 (1993), 179–219, Theorem 2.1.
* M. Rørdam, *Classification of Nuclear, Simple C⋆-Algebras*, Encyclopaedia Math. Sci. 126, §2.3,
  Corollary 2.3.3 and Theorem 2.3.4.
* E. Kirchberg and N. C. Phillips, *Embedding of exact C*-algebras in the Cuntz algebra O₂*,
  J. Reine Angew. Math. 525 (2000), 17–53, §1.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti

section UnitaryDiagram

private noncomputable def conjComp {X Y : Type*} [NonUnitalCStarAlgebra X] [CStarAlgebra Y]
    (w : unitary Y) (f : X →⋆ₙₐ[ℂ] Y) : X →⋆ₙₐ[ℂ] Y :=
  (Unitary.conjStarAlgAut ℂ Y w).toNonUnitalStarAlgHom.comp f

@[simp]
private theorem conjComp_apply {X Y : Type*} [NonUnitalCStarAlgebra X] [CStarAlgebra Y]
    (w : unitary Y) (f : X →⋆ₙₐ[ℂ] Y) (x : X) :
    conjComp w f x = (w : Y) * f x * star (w : Y) := by
  simp [conjComp, Unitary.conjStarAlgAut_apply]

private theorem exists_unitary_conjComp_le {X Y : Type*} [NonUnitalCStarAlgebra X] [CStarAlgebra Y]
    {f g : X →⋆ₙₐ[ℂ] Y} (h : ApproximatelyUnitarilyEquivalent f g)
    {S : Set X} (hS : S.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : unitary Y, ∀ ⦃x : X⦄, x ∈ S → ‖conjComp w f x - g x‖ ≤ ε := by
  rw [approximatelyUnitarilyEquivalent_def] at h
  obtain ⟨w, hw⟩ := h hS.toFinset ε hε
  refine ⟨w, fun x hx ↦ ?_⟩
  simpa only [conjComp_apply] using (hw x (hS.mem_toFinset.mpr hx)).le

private noncomputable def stageSeedSet {A : ℕ → Type*} [∀ m, NonUnitalCStarAlgebra (A m)]
    [∀ m, TopologicalSpace.SeparableSpace (A m)]
    (α : ∀ m, A m →⋆ₙₐ[ℂ] A (m + 1)) (n : ℕ) : Set (A n) :=
  ⋃ (m : ℕ) (hm : m ≤ n),
    NonUnitalStarAlgHom.natLERec α m n hm ∘ TopologicalSpace.denseSeq (A m) '' {k | k ≤ n}

private theorem finite_stageSeedSet {A : ℕ → Type*} [∀ m, NonUnitalCStarAlgebra (A m)]
    [∀ m, TopologicalSpace.SeparableSpace (A m)]
    (α : ∀ m, A m →⋆ₙₐ[ℂ] A (m + 1)) (n : ℕ) : (stageSeedSet α n).Finite :=
  (Set.finite_le_nat n).biUnion' fun _ _ ↦ (Set.finite_le_nat n).image _

private theorem mem_stageSeedSet {A : ℕ → Type*} [∀ m, NonUnitalCStarAlgebra (A m)]
    [∀ m, TopologicalSpace.SeparableSpace (A m)]
    (α : ∀ m, A m →⋆ₙₐ[ℂ] A (m + 1)) {m k n : ℕ} (hmn : m ≤ n) (hkn : k ≤ n) :
    NonUnitalStarAlgHom.natLERec α m n hmn (TopologicalSpace.denseSeq (A m) k) ∈
      stageSeedSet α n :=
  Set.mem_iUnion₂.mpr ⟨m, hmn, k, hkn, rfl⟩

private theorem approx_of_stageSeedSet {A : ℕ → Type*} [∀ m, NonUnitalCStarAlgebra (A m)]
    [∀ m, TopologicalSpace.SeparableSpace (A m)]
    {α : ∀ m, A m →⋆ₙₐ[ℂ] A (m + 1)} {F : ∀ m, Set (A m)}
    (hseed : ∀ m, stageSeedSet α m ⊆ F m) (n : ℕ) (x : A n) {ε : ℝ} (hε : 0 < ε) :
    ∃ m, ∃ hnm : n ≤ m, ∃ x' ∈ F m,
      ‖NonUnitalStarAlgHom.natLERec α n m hnm x - x'‖ < ε := by
  obtain ⟨k, hk⟩ :=
    Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq (A n)) x ε hε
  refine ⟨max n k, le_max_left n k,
    NonUnitalStarAlgHom.natLERec α n (max n k) (le_max_left n k)
      (TopologicalSpace.denseSeq (A n) k),
    hseed (max n k) (mem_stageSeedSet α (le_max_left n k) (le_max_right n k)), ?_⟩
  rw [← map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans_lt (by simpa only [dist_eq_norm] using hk)

private structure IntertwiningStep {A B : ℕ → Type*}
    [∀ m, CStarAlgebra (A m)] [∀ m, CStarAlgebra (B m)]
    (α : ∀ m, A m →⋆ₙₐ[ℂ] A (m + 1)) (β : ∀ m, B m →⋆ₙₐ[ℂ] B (m + 1))
    (φ₀ : ∀ m, A m →⋆ₙₐ[ℂ] B (m + 1)) (ψ₀ : ∀ m, B m →⋆ₙₐ[ℂ] A m) (n : ℕ) where
  G : Set (B n)
  finite_G : G.Finite
  u : unitary (A n)
  F : Set (A n)
  finite_F : F.Finite
  v : unitary (B (n + 1))
  mapsTo_psi : Set.MapsTo (conjComp u (ψ₀ n)) G F
  norm_B : ∀ ⦃y : B n⦄, y ∈ G →
    ‖conjComp v (φ₀ n) (conjComp u (ψ₀ n) y) - β n y‖ ≤ (1 / 2 : ℝ) ^ n

section StepConstruction

variable {A B : ℕ → Type*} [∀ m, CStarAlgebra (A m)] [∀ m, CStarAlgebra (B m)]
  {α : ∀ m, A m →⋆ₙₐ[ℂ] A (m + 1)} {β : ∀ m, B m →⋆ₙₐ[ℂ] B (m + 1)}
  {φ₀ : ∀ m, A m →⋆ₙₐ[ℂ] B (m + 1)} {ψ₀ : ∀ m, B m →⋆ₙₐ[ℂ] A m}

private theorem aue_phi_conjComp (hφ₀ : ∀ m, φ₀ m 1 = 1)
    (hB₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((φ₀ m).comp (ψ₀ m)) (β m))
    (n : ℕ) (u : unitary (A n)) :
    ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (conjComp u (ψ₀ n))) (β n) :=
  ((ApproximatelyUnitarilyEquivalent.conjStarAlgAut_comp u (ψ₀ n)).postcomp_of_map_one
    (φ₀ n) (hφ₀ n)).trans (hB₀ n)

private theorem aue_psi_conjComp (hψ₀ : ∀ m, ψ₀ (m + 1) 1 = 1)
    (hA₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((ψ₀ (m + 1)).comp (φ₀ m)) (α m))
    (n : ℕ) (v : unitary (B (n + 1))) :
    ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (conjComp v (φ₀ n))) (α n) :=
  ((ApproximatelyUnitarilyEquivalent.conjStarAlgAut_comp v (φ₀ n)).postcomp_of_map_one
    (ψ₀ (n + 1)) (hψ₀ n)).trans (hA₀ n)

variable [∀ m, TopologicalSpace.SeparableSpace (A m)]
  [∀ m, TopologicalSpace.SeparableSpace (B m)]

private noncomputable def baseIntertwiningStep (hφ₀ : ∀ m, φ₀ m 1 = 1)
    (hB₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((φ₀ m).comp (ψ₀ m)) (β m)) :
    IntertwiningStep α β φ₀ ψ₀ 0 :=
  let G₀ : Set (B 0) := stageSeedSet β 0
  have hG₀ : G₀.Finite := finite_stageSeedSet β 0
  let u₀ : unitary (A 0) := 1
  let F₀ : Set (A 0) := stageSeedSet α 0 ∪ conjComp u₀ (ψ₀ 0) '' G₀
  have hF₀ : F₀.Finite := (finite_stageSeedSet α 0).union (hG₀.image _)
  have hexB := exists_unitary_conjComp_le (aue_phi_conjComp hφ₀ hB₀ 0 u₀) hG₀
    (by positivity : (0 : ℝ) < (1 / 2) ^ 0)
  { G := G₀
    finite_G := hG₀
    u := u₀
    F := F₀
    finite_F := hF₀
    v := hexB.choose
    mapsTo_psi := fun _ hy ↦ Or.inr (Set.mem_image_of_mem _ hy)
    norm_B := fun _ hy ↦ hexB.choose_spec hy }

private noncomputable def nextIntertwiningStep (hφ₀ : ∀ m, φ₀ m 1 = 1)
    (hψ₀ : ∀ m, ψ₀ (m + 1) 1 = 1)
    (hA₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((ψ₀ (m + 1)).comp (φ₀ m)) (α m))
    (hB₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((φ₀ m).comp (ψ₀ m)) (β m))
    (n : ℕ) (s : IntertwiningStep α β φ₀ ψ₀ n) :
    IntertwiningStep α β φ₀ ψ₀ (n + 1) :=
  let G' : Set (B (n + 1)) :=
    stageSeedSet β (n + 1) ∪ β n '' s.G ∪ conjComp s.v (φ₀ n) '' s.F
  have hG' : G'.Finite :=
    ((finite_stageSeedSet β (n + 1)).union (s.finite_G.image _)).union (s.finite_F.image _)
  have hexA := exists_unitary_conjComp_le (aue_psi_conjComp hψ₀ hA₀ n s.v) s.finite_F
    (by positivity : (0 : ℝ) < (1 / 2) ^ n)
  let u' : unitary (A (n + 1)) := hexA.choose
  let F' : Set (A (n + 1)) :=
    stageSeedSet α (n + 1) ∪ α n '' s.F ∪ conjComp u' (ψ₀ (n + 1)) '' G'
  have hF' : F'.Finite :=
    ((finite_stageSeedSet α (n + 1)).union (s.finite_F.image _)).union (hG'.image _)
  have hexB := exists_unitary_conjComp_le (aue_phi_conjComp hφ₀ hB₀ (n + 1) u') hG'
    (by positivity : (0 : ℝ) < (1 / 2) ^ (n + 1))
  { G := G'
    finite_G := hG'
    u := u'
    F := F'
    finite_F := hF'
    v := hexB.choose
    mapsTo_psi := fun _ hy ↦ Or.inr (Set.mem_image_of_mem _ hy)
    norm_B := fun _ hy ↦ hexB.choose_spec hy }

private noncomputable def intertwiningStepSeq (hφ₀ : ∀ m, φ₀ m 1 = 1)
    (hψ₀ : ∀ m, ψ₀ (m + 1) 1 = 1)
    (hA₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((ψ₀ (m + 1)).comp (φ₀ m)) (α m))
    (hB₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((φ₀ m).comp (ψ₀ m)) (β m)) :
    ∀ n, IntertwiningStep α β φ₀ ψ₀ n
  | 0 => baseIntertwiningStep hφ₀ hB₀
  | n + 1 => nextIntertwiningStep hφ₀ hψ₀ hA₀ hB₀ n (intertwiningStepSeq hφ₀ hψ₀ hA₀ hB₀ n)

private theorem seed_F_intertwiningStepSeq (hφ₀ : ∀ m, φ₀ m 1 = 1)
    (hψ₀ : ∀ m, ψ₀ (m + 1) 1 = 1)
    (hA₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((ψ₀ (m + 1)).comp (φ₀ m)) (α m))
    (hB₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((φ₀ m).comp (ψ₀ m)) (β m)) (n : ℕ) :
    stageSeedSet α n ⊆ (intertwiningStepSeq hφ₀ hψ₀ hA₀ hB₀ n).F := by
  cases n with
  | zero => exact Set.subset_union_left
  | succ m => exact fun _ hx ↦ Or.inl (Or.inl hx)

private theorem seed_G_intertwiningStepSeq (hφ₀ : ∀ m, φ₀ m 1 = 1)
    (hψ₀ : ∀ m, ψ₀ (m + 1) 1 = 1)
    (hA₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((ψ₀ (m + 1)).comp (φ₀ m)) (α m))
    (hB₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((φ₀ m).comp (ψ₀ m)) (β m)) (n : ℕ) :
    stageSeedSet β n ⊆ (intertwiningStepSeq hφ₀ hψ₀ hA₀ hB₀ n).G := by
  cases n with
  | zero => exact Set.Subset.rfl
  | succ m => exact fun _ hy ↦ Or.inl (Or.inl hy)

private theorem norm_A_nextIntertwiningStep (hφ₀ : ∀ m, φ₀ m 1 = 1)
    (hψ₀ : ∀ m, ψ₀ (m + 1) 1 = 1)
    (hA₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((ψ₀ (m + 1)).comp (φ₀ m)) (α m))
    (hB₀ : ∀ m, ApproximatelyUnitarilyEquivalent ((φ₀ m).comp (ψ₀ m)) (β m))
    (n : ℕ) (s : IntertwiningStep α β φ₀ ψ₀ n) ⦃x : A n⦄ (hx : x ∈ s.F) :
    ‖conjComp (nextIntertwiningStep hφ₀ hψ₀ hA₀ hB₀ n s).u (ψ₀ (n + 1))
        (conjComp s.v (φ₀ n) x) - α n x‖ ≤ (1 / 2 : ℝ) ^ n := by
  dsimp only [nextIntertwiningStep]
  exact (exists_unitary_conjComp_le (aue_psi_conjComp hψ₀ hA₀ n s.v) s.finite_F
    (by positivity : (0 : ℝ) < (1 / 2) ^ n)).choose_spec hx

end StepConstruction

/-- **Unitary conjugation of approximately commuting diagrams** (Elliott, Theorem 2.1; Rørdam, §2.3,
Corollary 2.3.3): if `φ₀ n : A n →⋆ₙₐ[ℂ] B (n + 1)` and `ψ₀ n : B n →⋆ₙₐ[ℂ] A n` between sequential
systems of separable unital C⋆-algebras preserve units (`φ₀ n 1 = 1`, `ψ₀ (n + 1) 1 = 1`) and make
every triangle commute up to `ApproximatelyUnitarilyEquivalent`, then there exist unitary sequences
`u : ∀ n, unitary (A n)` and `v : ∀ n, unitary (B (n + 1))` whose conjugates `Ad(v n) ∘ φ₀ n` and
`Ad(u n) ∘ ψ₀ n` form an `ApproximateIntertwining`. -/
theorem ApproximateIntertwining.exists_of_approximatelyUnitarilyEquivalent
    {A B : ℕ → Type*} [∀ n, CStarAlgebra (A n)] [∀ n, CStarAlgebra (B n)]
    [∀ n, TopologicalSpace.SeparableSpace (A n)] [∀ n, TopologicalSpace.SeparableSpace (B n)]
    (α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)) (β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1))
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hφ₀ : ∀ n, φ₀ n 1 = 1) (hψ₀ : ∀ n, ψ₀ (n + 1) 1 = 1)
    (hA₀ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hB₀ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n)) :
    ∃ (u : ∀ n, unitary (A n)) (v : ∀ n, unitary (B (n + 1))),
      Nonempty (ApproximateIntertwining α β
        (fun n ↦ (Unitary.conjStarAlgAut ℂ (B (n + 1)) (v n)).toNonUnitalStarAlgHom.comp (φ₀ n))
        (fun n ↦ (Unitary.conjStarAlgAut ℂ (A n) (u n)).toNonUnitalStarAlgHom.comp (ψ₀ n))) := by
  let S := intertwiningStepSeq hφ₀ hψ₀ hA₀ hB₀
  refine ⟨fun n ↦ (S n).u, fun n ↦ (S n).v, ⟨?_⟩⟩
  refine
    { F := fun n ↦ (S n).F
      G := fun n ↦ (S n).G
      δA := fun n ↦ (1 / 2 : ℝ) ^ n
      δB := fun n ↦ (1 / 2 : ℝ) ^ n
      summable_δA := summable_geometric_two
      summable_δB := summable_geometric_two
      norm_psi_phi_sub_le := fun n x hx ↦ norm_A_nextIntertwiningStep hφ₀ hψ₀ hA₀ hB₀ n (S n) hx
      norm_phi_psi_sub_le := fun n y hy ↦ (S n).norm_B hy
      mapsTo_alpha := fun n x hx ↦ Or.inl (Or.inr (Set.mem_image_of_mem _ hx))
      mapsTo_beta := fun n y hy ↦ Or.inl (Or.inr (Set.mem_image_of_mem _ hy))
      mapsTo_phi := fun n x hx ↦ Or.inr (Set.mem_image_of_mem _ hx)
      mapsTo_psi := fun n ↦ (S n).mapsTo_psi
      approx_A := approx_of_stageSeedSet (seed_F_intertwiningStepSeq hφ₀ hψ₀ hA₀ hB₀)
      approx_B := approx_of_stageSeedSet (seed_G_intertwiningStepSeq hφ₀ hψ₀ hA₀ hB₀) }

/-- **Sequential C⋆-limit isomorphism from approximate unitary equivalence** (Elliott, Theorem 2.1;
Rørdam, §2.3, Theorem 2.3.4): if `(C, ιA)` and `(D, ιB)` are sequential C⋆-inductive limits of
systems `(A, α)` and `(B, β)` of separable unital C⋆-algebras, and `φ₀ n : A n →⋆ₙₐ[ℂ] B (n + 1)`
(`φ₀ n 1 = 1`) and `ψ₀ n : B n →⋆ₙₐ[ℂ] A n` (`ψ₀ (n + 1) 1 = 1`) make each triangle commute up to
`ApproximatelyUnitarilyEquivalent`, then there exist unitary sequences `u : ∀ n, unitary (A n)` and
`v : ∀ n, unitary (B (n + 1))` and a `⋆`-isomorphism `θ : C ≃⋆ₐ[ℂ] D` induced by the pointwise
limits of the unitarily conjugated stage maps. -/
theorem IsSequentialCStarLimit.exists_starAlgEquiv_of_approximatelyUnitarilyEquivalent
    {A B : ℕ → Type*} [∀ n, CStarAlgebra (A n)] [∀ n, CStarAlgebra (B n)]
    [∀ n, TopologicalSpace.SeparableSpace (A n)] [∀ n, TopologicalSpace.SeparableSpace (B n)]
    {C D : Type*} [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    {α : ∀ n, A n →⋆ₙₐ[ℂ] A (n + 1)} {β : ∀ n, B n →⋆ₙₐ[ℂ] B (n + 1)}
    {ιA : ∀ n, A n →⋆ₙₐ[ℂ] C} {ιB : ∀ n, B n →⋆ₙₐ[ℂ] D}
    (hA : IsSequentialCStarLimit α ιA) (hB : IsSequentialCStarLimit β ιB)
    (φ₀ : ∀ n, A n →⋆ₙₐ[ℂ] B (n + 1)) (ψ₀ : ∀ n, B n →⋆ₙₐ[ℂ] A n)
    (hφ₀ : ∀ n, φ₀ n 1 = 1) (hψ₀ : ∀ n, ψ₀ (n + 1) 1 = 1)
    (hA₀ : ∀ n, ApproximatelyUnitarilyEquivalent ((ψ₀ (n + 1)).comp (φ₀ n)) (α n))
    (hB₀ : ∀ n, ApproximatelyUnitarilyEquivalent ((φ₀ n).comp (ψ₀ n)) (β n)) :
    ∃ (u : ∀ n, unitary (A n)) (v : ∀ n, unitary (B (n + 1))) (θ : C ≃⋆ₐ[ℂ] D),
      (∀ n (x : A n),
        Tendsto (fun k ↦
          ιB (n + k + 1)
            ((v (n + k) : B (n + k + 1)) *
              φ₀ (n + k) (NonUnitalStarAlgHom.natLERec α n (n + k) (Nat.le_add_right n k) x) *
              star (v (n + k) : B (n + k + 1))))
          atTop (𝓝 (θ (ιA n x)))) ∧
      (∀ n (y : B n),
        Tendsto (fun k ↦
          ιA (n + k)
            ((u (n + k) : A (n + k)) *
              ψ₀ (n + k) (NonUnitalStarAlgHom.natLERec β n (n + k) (Nat.le_add_right n k) y) *
              star (u (n + k) : A (n + k))))
          atTop (𝓝 (θ.symm (ιB n y)))) := by
  obtain ⟨u, v, ⟨H⟩⟩ :=
    ApproximateIntertwining.exists_of_approximatelyUnitarilyEquivalent α β φ₀ ψ₀ hφ₀ hψ₀ hA₀ hB₀
  refine ⟨u, v, H.equiv hA hB, fun n x ↦ ?_, fun n y ↦ ?_⟩
  · simpa only [NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
      Unitary.conjStarAlgAut_apply] using H.tendsto_equiv_apply hA hB n x
  · simpa only [NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
      Unitary.conjStarAlgAut_apply] using H.tendsto_equiv_symm_apply hA hB n y

end UnitaryDiagram

/-- **Elliott's approximate intertwining theorem** for mutual approximate unitary inverses between
separable unital C⋆-algebras (Elliott, Theorem 2.1; Kirchberg–Phillips, §1; Rørdam, Corollary
2.3.3): if `φ : A →⋆ₙₐ[ℂ] B` and `ψ : B →⋆ₙₐ[ℂ] A` satisfy `ψ ∘ φ ≈_u id_A` and `φ ∘ ψ ≈_u id_B`,
then there exists a `⋆`-isomorphism `θ : A ≃⋆ₐ[ℂ] B` approximately unitarily equivalent to `φ`. -/
theorem elliott_intertwining {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] A)
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A))
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (NonUnitalStarAlgHom.id ℂ B)) :
    ∃ θ : A ≃⋆ₐ[ℂ] B, ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ := by
  obtain ⟨_, v, θ, hθ, _⟩ :=
    (IsSequentialCStarLimit.const A).exists_starAlgEquiv_of_approximatelyUnitarilyEquivalent
      (IsSequentialCStarLimit.const B) (fun _ ↦ φ) (fun _ ↦ ψ)
      (fun _ ↦ hφψ.map_one_of_comp_id) (fun _ ↦ hψφ.map_one_of_comp_id)
      (fun _ ↦ hψφ) (fun _ ↦ hφψ)
  refine ⟨θ, (ApproximatelyUnitarilyEquivalent.of_tendsto (l := atTop) v fun a ↦ ?_).symm⟩
  simpa only [Nat.zero_add, NonUnitalStarAlgHom.natLERec_id, NonUnitalStarAlgHom.coe_id, id_eq,
    StarAlgEquiv.toNonUnitalStarAlgHom_apply] using hθ 0 a

end TauCeti
