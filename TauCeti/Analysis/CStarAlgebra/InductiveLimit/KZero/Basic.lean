/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.InductiveLimit.Basic
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero
import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import TauCeti.Analysis.CStarAlgebra.Matrix.EntryNorm
import TauCeti.Analysis.CStarAlgebra.Projection.Approximate
import TauCeti.Analysis.CStarAlgebra.Projection.Perturbation

/-!
# Continuity of `V` and `K₀` along C⋆-inductive limits

Let `(A i, f i j)` be a directed system of C⋆-algebras, possibly without unit and with connecting
maps that need not be injective, and `L = CStarInductiveLimit A f` its C⋆-inductive limit with
canonical maps `of i : A i → L`. The projection monoid `V(L)` and its Grothendieck group `K₀(L)`
are the colimits of those of the stages:

* every matrix projection over `L` is Murray–von Neumann equivalent to the image of a matrix
  projection over some stage
  (`TauCeti.CStarInductiveLimit.exists_isMurrayVonNeumannEquivalent_map_of`);
* matrix projections over `A i` whose images in `L` are equivalent become equivalent in some
  later stage (`TauCeti.CStarInductiveLimit.exists_isMurrayVonNeumannEquivalent_map_f`).

Consequently every element of `V(L)` and of `K₀(L)` comes from a stage, and two elements of
`V(A i)`, or of `K₀(A i)`, with the same image in `V(L)`, or `K₀(L)`, have the same image in some
later stage (`TauCeti.CStarInductiveLimit.exists_projectionMonoid_map_of_eq`,
`TauCeti.CStarInductiveLimit.exists_projectionMonoid_map_f_eq_of_map_of_eq` and their
`ProjectionKZero` versions). For a directed system of unital C⋆-algebras along unital maps,
`TauCeti.ProjectionKZero` is the operator `K₀`-group, so this is the continuity of `K₀`.

The proofs perturb. A projection `P` over `L` is approximated by the image of a self-adjoint
matrix `x` over a stage, whose defect `x - x * x` becomes small in a later stage since the norm in
`L` of an element of a stage is the infimum of the norms of its images in the later stages; the
rounding of `x` (`TauCeti.exists_isStarProjection_norm_sub_le`) is then a projection whose image
is within distance `1` of `P`, hence equivalent to `P`. For the injectivity, the projections are
padded to ones of the same size; a partial isometry implementing the equivalence in `L` is
approximated from a stage and compressed between the two projections, and the resulting
approximate partial isometry becomes good enough in a later stage to give an exact equivalence
there (`IsStarProjection.exists_star_mul_self_eq_of_norm_star_mul_self_sub_lt_one`).

## Main statements

* `TauCeti.CStarInductiveLimit.exists_isMurrayVonNeumannEquivalent_map_of`
* `TauCeti.CStarInductiveLimit.exists_isMurrayVonNeumannEquivalent_map_f`
* `TauCeti.CStarInductiveLimit.exists_projectionMonoid_map_of_eq`
* `TauCeti.CStarInductiveLimit.exists_projectionMonoid_map_f_eq_of_map_of_eq`
* `TauCeti.CStarInductiveLimit.exists_projectionKZero_map_of_eq`
* `TauCeti.CStarInductiveLimit.exists_projectionKZero_map_f_eq_zero_of_map_of_eq_zero`

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  5.2.4.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

namespace CStarInductiveLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {A : ι → Type*}
  [∀ i, NonUnitalCStarAlgebra (A i)] {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
  [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
  [∀ i j (h : i ≤ j), NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
  [∀ i j (h : i ≤ j), StarHomClass (T h) (A i) (A j)] [DirectedSystem A (f · · ·)]

section Matrix

variable {N : Type*} [Fintype N]

/-- The canonical maps on matrices are compatible with the connecting maps. -/
private theorem mapₙₐ_of_mapₙₐ_f {i j : ι} (hij : i ≤ j) (M : CStarMatrix N N (A i)) :
    CStarMatrix.mapₙₐ (of A f j)
        (CStarMatrix.mapₙₐ (NonUnitalStarAlgHom.ofClass (f i j hij)) M) =
      CStarMatrix.mapₙₐ (of A f i) M :=
  CStarMatrix.ext fun _ _ => of_f hij _

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- The connecting maps on matrices compose. -/
private theorem mapₙₐ_f_mapₙₐ_f {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (M : CStarMatrix N N (A i)) :
    CStarMatrix.mapₙₐ (NonUnitalStarAlgHom.ofClass (f j k hjk))
        (CStarMatrix.mapₙₐ (NonUnitalStarAlgHom.ofClass (f i j hij)) M) =
      CStarMatrix.mapₙₐ (NonUnitalStarAlgHom.ofClass (f i k (hij.trans hjk))) M :=
  CStarMatrix.ext fun _ _ => DirectedSystem.map_map (f := (f · · ·)) hij hjk _

/-- The numerical facts behind the perturbation estimates: for `n ≥ 0`, `c = n² + 1`,
`ε = 1 / (64 c²)` and `η = n² ε`, we have `0 < ε`, `η ≤ 1/64` and `n² η ≤ 1/64`. -/
private theorem estimates (n : ℝ) (hn : 0 ≤ n) :
    0 < 1 / (64 * (n * n + 1) * (n * n + 1)) ∧
      n * n * (1 / (64 * (n * n + 1) * (n * n + 1))) ≤ 1 / 64 ∧
      n * n * (n * n * (1 / (64 * (n * n + 1) * (n * n + 1)))) ≤ 1 / 64 := by
  have hnc : n * n ≤ n * n + 1 := by linarith
  have hε : 0 < 1 / (64 * (n * n + 1) * (n * n + 1)) := by positivity
  have h₁ : n * n * (1 / (64 * (n * n + 1) * (n * n + 1))) ≤ 1 / (64 * (n * n + 1)) :=
    calc n * n * (1 / (64 * (n * n + 1) * (n * n + 1)))
        ≤ (n * n + 1) * (1 / (64 * (n * n + 1) * (n * n + 1))) := by gcongr
      _ = 1 / (64 * (n * n + 1)) := by field_simp
  have h₂ : 1 / (64 * (n * n + 1)) ≤ 1 / 64 := by
    gcongr
    linarith [mul_nonneg hn hn]
  refine ⟨hε, h₁.trans h₂, ?_⟩
  calc n * n * (n * n * (1 / (64 * (n * n + 1) * (n * n + 1))))
      ≤ (n * n + 1) * (1 / (64 * (n * n + 1))) := by gcongr
    _ = 1 / 64 := by field_simp

/-- **Approximating matrices over the limit.** A matrix over the C⋆-inductive limit is within
`card N ^ 2 * ε` of the image of a matrix over a stage, which can be taken above any index. -/
private theorem exists_norm_mapₙₐ_sub_le (M : CStarMatrix N N (CStarInductiveLimit A f))
    (i₀ : ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ k, i₀ ≤ k ∧ ∃ Y : CStarMatrix N N (A k),
      ‖CStarMatrix.mapₙₐ (of A f k) Y - M‖ ≤ Fintype.card N * Fintype.card N * ε := by
  obtain ⟨k, hk, y, hy⟩ := exists_forall_norm_of_sub_lt (fun b : N × N => M b.1 b.2) i₀ hε
  exact ⟨k, hk, CStarMatrix.ofMatrix (Matrix.of fun a b => y (a, b)),
    CStarMatrix.norm_le_card_mul_of_forall_norm_entry_le _ fun a b => (hy (a, b)).le⟩

/-- **Uniform decay of matrices.** If finitely many matrices over `A k` have images of norm
`< c` over the C⋆-inductive limit, their images over some later stage have norm at most
`card N ^ 2 * c`. -/
private theorem exists_forall_norm_mapₙₐ_le [∀ i, PartialOrder (A i)]
    [∀ i, StarOrderedRing (A i)] {β : Type*} [Finite β] {k : ι}
    (E : β → CStarMatrix N N (A k)) {c : ℝ}
    (h : ∀ b, ‖CStarMatrix.mapₙₐ (of A f k) (E b)‖ < c) :
    ∃ j, ∃ hkj : k ≤ j, ∀ b,
      ‖CStarMatrix.mapₙₐ (NonUnitalStarAlgHom.ofClass (f k j hkj)) (E b)‖ ≤
        Fintype.card N * Fintype.card N * c := by
  obtain ⟨j, hkj, hj⟩ := exists_forall_norm_lt (f := f)
    (fun b : β × N × N => E b.1 b.2.1 b.2.2) fun b =>
      (CStarMatrix.norm_entry_le_norm (M := CStarMatrix.mapₙₐ (of A f k) (E b.1))).trans_lt
        (h b.1)
  exact ⟨j, hkj, fun b => CStarMatrix.norm_le_card_mul_of_forall_norm_entry_le _
    fun a a' => (hj (b, a, a')).le⟩

/-- **Lifting projections, matrix form.** A projection `P` over the C⋆-inductive limit is within
distance `1` of the image of a projection over some stage. -/
private theorem exists_isStarProjection_norm_mapₙₐ_sub_lt_one
    {P : CStarMatrix N N (CStarInductiveLimit A f)} (hP : IsStarProjection P) :
    ∃ i, ∃ p : CStarMatrix N N (A i), IsStarProjection p ∧
      ‖CStarMatrix.mapₙₐ (of A f i) p - P‖ < 1 := by
  classical
  let _ (i : ι) : PartialOrder (A i) := CStarAlgebra.spectralOrder (A i)
  let _ (i : ι) : StarOrderedRing (A i) := CStarAlgebra.spectralOrderedRing (A i)
  set n : ℝ := (Fintype.card N : ℝ)
  obtain ⟨hε, hη, hnη⟩ := estimates n (Nat.cast_nonneg _)
  set ε := 1 / (64 * (n * n + 1) * (n * n + 1))
  set η := n * n * ε
  -- approximate `P` from a stage, and take the self-adjoint part `X`
  obtain ⟨i, -, Y, hYP⟩ := exists_norm_mapₙₐ_sub_le P (Classical.arbitrary ι) hε
  set φ := CStarMatrix.mapₙₐ (n := N) (of A f i)
  set X : CStarMatrix N N (A i) := (1 / 2 : ℂ) • (Y + star Y)
  have hX : IsSelfAdjoint X := by
    refine IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) ?_
    simp [IsSelfAdjoint, add_comm]
  have hXP : ‖φ X - P‖ ≤ η := by
    have he : φ X - P = (1 / 2 : ℂ) • ((φ Y - P) + star (φ Y - P)) := by
      rw [star_sub, hP.isSelfAdjoint.star_eq, map_smul, map_add, map_star]
      module
    rw [he, norm_smul]
    calc ‖(1 / 2 : ℂ)‖ * ‖φ Y - P + star (φ Y - P)‖ ≤ 1 / 2 * (η + η) := by
          gcongr
          · simp
          · exact norm_add_le_of_le hYP (by rwa [norm_star])
      _ = η := by ring
  have hdef : ‖φ (X - X * X)‖ ≤ 4 * η := by
    rw [map_sub, map_mul]
    exact hP.norm_sub_mul_self_le hXP (by linarith)
  -- in a later stage the defect is at most `n² (4 η + ε)`; round there
  obtain ⟨j, hij, hj⟩ := exists_forall_norm_mapₙₐ_le (f := f) (fun _ : Unit => X - X * X)
    (c := 4 * η + ε) fun _ => hdef.trans_lt (by linarith)
  set ψ := CStarMatrix.mapₙₐ (n := N) (NonUnitalStarAlgHom.ofClass (f i j hij))
  have hXj : ‖ψ X - ψ X * ψ X‖ ≤ n * n * (4 * η + ε) := by
    rw [← map_mul, ← map_sub]
    exact hj ()
  obtain ⟨p, hp, hpX⟩ := exists_isStarProjection_norm_sub_le (hX.map ψ) hXj (by linarith)
  refine ⟨j, p, hp, ?_⟩
  have hφ : CStarMatrix.mapₙₐ (of A f j) (ψ X) = φ X := mapₙₐ_of_mapₙₐ_f hij X
  calc ‖CStarMatrix.mapₙₐ (of A f j) p - P‖
      = ‖CStarMatrix.mapₙₐ (of A f j) (p - ψ X) + (φ X - P)‖ := by
        rw [map_sub, hφ]
        abel_nf
    _ ≤ ‖p - ψ X‖ + η := norm_add_le_of_le (NonUnitalStarAlgHom.norm_apply_le _ _) hXP
    _ ≤ 2 * (n * n * (4 * η + ε)) + η := by
        gcongr
        rwa [norm_sub_rev]
    _ < 1 := by linarith

/-- **Approximate equivalence descends, matrix form.** If projections `p` and `q` over `A i` have
images in the C⋆-inductive limit that are equivalent through a partial isometry `v`, they become
equivalent in some later stage. -/
private theorem exists_star_mul_self_eq_mapₙₐ_f {i : ι}
    {p q : CStarMatrix N N (A i)} (hp : IsStarProjection p) (hq : IsStarProjection q)
    {v : CStarMatrix N N (CStarInductiveLimit A f)}
    (hv₁ : star v * v = CStarMatrix.mapₙₐ (of A f i) p)
    (hv₂ : v * star v = CStarMatrix.mapₙₐ (of A f i) q) :
    ∃ j, ∃ hij : i ≤ j, ∃ u : CStarMatrix N N (A j),
      star u * u = CStarMatrix.mapₙₐ (NonUnitalStarAlgHom.ofClass (f i j hij)) p ∧
      u * star u = CStarMatrix.mapₙₐ (NonUnitalStarAlgHom.ofClass (f i j hij)) q := by
  classical
  let _ (i : ι) : PartialOrder (A i) := CStarAlgebra.spectralOrder (A i)
  let _ (i : ι) : StarOrderedRing (A i) := CStarAlgebra.spectralOrderedRing (A i)
  set n : ℝ := (Fintype.card N : ℝ)
  obtain ⟨hε, hη, hnη⟩ := estimates n (Nat.cast_nonneg _)
  set ε := 1 / (64 * (n * n + 1) * (n * n + 1))
  set η := n * n * ε
  -- approximate `v` from a stage `k ≥ i` and compress between the images of `q` and `p`
  obtain ⟨k, hik, Y, hYv⟩ := exists_norm_mapₙₐ_sub_le v i hε
  replace hYv : ‖CStarMatrix.mapₙₐ (of A f k) Y - v‖ ≤ η := hYv
  set ψ := CStarMatrix.mapₙₐ (n := N) (NonUnitalStarAlgHom.ofClass (f i k hik))
  have hφkψ (M : CStarMatrix N N (A i)) :
      CStarMatrix.mapₙₐ (of A f k) (ψ M) = CStarMatrix.mapₙₐ (of A f i) M :=
    mapₙₐ_of_mapₙₐ_f hik M
  set w := ψ q * Y * ψ p with hw_def
  obtain ⟨hE₁, hE₂⟩ := (hp.map _).norm_compress_sub_le hv₁ hv₂ hYv (by linarith)
  simp only [← hφkψ, ← map_mul, ← map_star, ← map_sub] at hE₁ hE₂
  -- in a later stage `j` both defects are at most `n² (3 η + ε)`
  obtain ⟨j, hkj, hj⟩ := exists_forall_norm_mapₙₐ_le (f := f)
    (fun b : Bool => if b then star w * w - ψ p else w * star w - ψ q) (c := 3 * η + ε)
    fun b => by
      have h3 : 3 * η < 3 * η + ε := by linarith
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        exact hE₂.trans_lt h3
      · simp only [ite_true]
        exact hE₁.trans_lt h3
  set χ := CStarMatrix.mapₙₐ (n := N) (NonUnitalStarAlgHom.ofClass (f k j hkj))
  have hχψ (M : CStarMatrix N N (A i)) :
      χ (ψ M) = CStarMatrix.mapₙₐ (NonUnitalStarAlgHom.ofClass (f i j (hik.trans hkj))) M :=
    mapₙₐ_f_mapₙₐ_f hik hkj M
  have hpp : ψ p * ψ p = ψ p := (hp.map ψ).isIdempotentElem.eq
  have hqq : ψ q * ψ q = ψ q := (hq.map ψ).isIdempotentElem.eq
  have hw' : ψ q * w * ψ p = w := by
    simp only [hw_def, ← mul_assoc, hqq]
    simp only [mul_assoc, hpp]
  have h₁ := hj true
  have h₂ := hj false
  simp only [ite_true, Bool.false_eq_true, ite_false, map_sub, map_mul, map_star] at h₁ h₂
  obtain ⟨u, hu₁, hu₂⟩ :=
    IsStarProjection.exists_star_mul_self_eq_of_norm_star_mul_self_sub_lt_one
      ((hp.map ψ).map χ) ((hq.map ψ).map χ) (by rw [← map_mul, ← map_mul, hw'])
      (by linarith) (by linarith)
  exact ⟨j, hik.trans hkj, u, by rw [hu₁, hχψ], by rw [hu₂, hχψ]⟩

/-- **Lifting projections.** Every matrix projection over the C⋆-inductive limit is
Murray–von Neumann equivalent to the image of a matrix projection of the same size over some
stage. -/
theorem exists_isMurrayVonNeumannEquivalent_map_of {P : Matrix N N (CStarInductiveLimit A f)}
    (hP : IsStarProjection P) :
    ∃ i, ∃ p : Matrix N N (A i), IsStarProjection p ∧
      IsMurrayVonNeumannEquivalent (p.map (of A f i)) P := by
  classical
  have hP' : IsStarProjection (CStarMatrix.ofMatrix P) :=
    CStarMatrix.isStarProjection_ofMatrix_iff.2 hP
  obtain ⟨i, p, hp, hpP⟩ := exists_isStarProjection_norm_mapₙₐ_sub_lt_one hP'
  have hφp : IsStarProjection (CStarMatrix.mapₙₐ (of A f i) p) := hp.map _
  obtain ⟨v, hv₁, hv₂⟩ := hφp.exists_star_mul_self_eq_of_norm_sub_lt_one hP' hpP
  refine ⟨i, CStarMatrix.ofMatrix.symm p, CStarMatrix.isStarProjection_ofMatrix_symm_iff.2 hp,
    ?_⟩
  simpa using CStarMatrix.isMurrayVonNeumannEquivalent_of_star_mul_self_eq hφp hP' hv₁ hv₂

/-- **Equivalence descends, same size.** If matrix projections `p` and `q` over `A i` of the same
size have Murray–von Neumann equivalent images in the C⋆-inductive limit, their images in some
later stage are equivalent. -/
private theorem exists_isMurrayVonNeumannEquivalent_map_f_of_same_size {i : ι}
    {p q : Matrix N N (A i)} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : IsMurrayVonNeumannEquivalent (p.map (of A f i)) (q.map (of A f i))) :
    ∃ j, ∃ hij : i ≤ j,
      IsMurrayVonNeumannEquivalent (p.map (f i j hij)) (q.map (f i j hij)) := by
  classical
  obtain ⟨v, hv₁, hv₂, -⟩ := h.exists_mul_conjTranspose_mul_self_eq
  have hp' : IsStarProjection (CStarMatrix.ofMatrix p) :=
    CStarMatrix.isStarProjection_ofMatrix_iff.2 hp
  have hq' : IsStarProjection (CStarMatrix.ofMatrix q) :=
    CStarMatrix.isStarProjection_ofMatrix_iff.2 hq
  obtain ⟨j, hij, u, hu₁, hu₂⟩ := exists_star_mul_self_eq_mapₙₐ_f hp' hq'
    (v := CStarMatrix.ofMatrix v)
    (CStarMatrix.ofMatrix.symm.injective (by
      simp [CStarMatrix.ofMatrix_symm_mul, CStarMatrix.ofMatrix_symm_star, hv₁]))
    (CStarMatrix.ofMatrix.symm.injective (by
      simp [CStarMatrix.ofMatrix_symm_mul, CStarMatrix.ofMatrix_symm_star, hv₂]))
  refine ⟨j, hij, ?_⟩
  simpa using
    CStarMatrix.isMurrayVonNeumannEquivalent_of_star_mul_self_eq (hp'.map _) (hq'.map _) hu₁ hu₂

/-- **Equivalence descends.** If matrix projections `p` and `q` over `A i`, of possibly different
sizes, have Murray–von Neumann equivalent images in the C⋆-inductive limit, their images in some
later stage are equivalent. -/
theorem exists_isMurrayVonNeumannEquivalent_map_f {m n : Type*} [Fintype m] [Fintype n] {i : ι}
    {p : Matrix m m (A i)} {q : Matrix n n (A i)} (hp : IsStarProjection p)
    (hq : IsStarProjection q)
    (h : IsMurrayVonNeumannEquivalent (p.map (of A f i)) (q.map (of A f i))) :
    ∃ j, ∃ hij : i ≤ j,
      IsMurrayVonNeumannEquivalent (p.map (f i j hij)) (q.map (f i j hij)) := by
  -- pad `p` and `q` to projections of the same size
  have hP : IsStarProjection (fromBlocks p 0 0 (0 : Matrix n n (A i))) :=
    hp.fromBlocks_zero₁₂_zero₂₁ (.zero _)
  have hQ : IsStarProjection (fromBlocks (0 : Matrix m m (A i)) 0 0 q) :=
    (IsStarProjection.zero _).fromBlocks_zero₁₂_zero₂₁ hq
  have hmap : IsMurrayVonNeumannEquivalent
      ((fromBlocks p 0 0 (0 : Matrix n n (A i))).map (of A f i))
      ((fromBlocks (0 : Matrix m m (A i)) 0 0 q).map (of A f i)) := by
    simpa [fromBlocks_map] using
      ((hp.matrix_map _).isMurrayVonNeumannEquivalent_fromBlocks_iff (hq.matrix_map _)).2 h
  obtain ⟨j, hij, hj⟩ := exists_isMurrayVonNeumannEquivalent_map_f_of_same_size hP hQ hmap
  refine ⟨j, hij, ?_⟩
  rw [← (hp.matrix_map _).isMurrayVonNeumannEquivalent_fromBlocks_iff (hq.matrix_map _)]
  simpa [fromBlocks_map] using hj

end Matrix

section ProjectionMonoid

open NonUnitalStarRingHom (ofClass)

/-- The maps induced on `V` by the canonical maps are compatible with the connecting maps. -/
@[simp]
theorem projectionMonoid_map_of_map_f {i j : ι} (hij : i ≤ j) (y : ProjectionMonoid (A i)) :
    ProjectionMonoid.map (ofClass (of A f j)) (ProjectionMonoid.map (ofClass (f i j hij)) y) =
      ProjectionMonoid.map (ofClass (of A f i)) y := by
  rw [ProjectionMonoid.map_map]
  congr 2
  ext a
  exact of_f hij a

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- The maps induced on `V` by the connecting maps compose. -/
@[simp]
theorem projectionMonoid_map_f_map_f {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (y : ProjectionMonoid (A i)) :
    ProjectionMonoid.map (ofClass (f j k hjk)) (ProjectionMonoid.map (ofClass (f i j hij)) y) =
      ProjectionMonoid.map (ofClass (f i k (hij.trans hjk))) y := by
  rw [ProjectionMonoid.map_map]
  congr 2
  ext a
  exact DirectedSystem.map_map (f := (f · · ·)) hij hjk a

/-- The maps induced on `K₀` by the canonical maps are compatible with the connecting maps. -/
@[simp]
theorem projectionKZero_map_of_map_f {i j : ι} (hij : i ≤ j) (y : ProjectionKZero (A i)) :
    ProjectionKZero.map (ofClass (of A f j)) (ProjectionKZero.map (ofClass (f i j hij)) y) =
      ProjectionKZero.map (ofClass (of A f i)) y := by
  rw [ProjectionKZero.map_map]
  congr 2
  ext a
  exact of_f hij a

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- The maps induced on `K₀` by the connecting maps compose. -/
@[simp]
theorem projectionKZero_map_f_map_f {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (y : ProjectionKZero (A i)) :
    ProjectionKZero.map (ofClass (f j k hjk)) (ProjectionKZero.map (ofClass (f i j hij)) y) =
      ProjectionKZero.map (ofClass (f i k (hij.trans hjk))) y := by
  rw [ProjectionKZero.map_map]
  congr 2
  ext a
  exact DirectedSystem.map_map (f := (f · · ·)) hij hjk a

/-- **Continuity of `V`, surjectivity.** Every element of the projection monoid of the
C⋆-inductive limit is the image of an element of the projection monoid of some stage. -/
theorem exists_projectionMonoid_map_of_eq (x : ProjectionMonoid (CStarInductiveLimit A f)) :
    ∃ i, ∃ y : ProjectionMonoid (A i), ProjectionMonoid.map (ofClass (of A f i)) y = x := by
  induction x using ProjectionMonoid.ind with
  | mk k P hP =>
    obtain ⟨i, p, hp, h⟩ := exists_isMurrayVonNeumannEquivalent_map_of hP
    exact ⟨i, ProjectionMonoid.mk p hp, by
      rw [ProjectionMonoid.map_mk]
      exact (ProjectionMonoid.mk_eq_mk_iff _ _).2 h⟩

/-- **Continuity of `V`, injectivity.** Two elements of the projection monoid of a stage with the
same image in the projection monoid of the C⋆-inductive limit have the same image in some later
stage. -/
theorem exists_projectionMonoid_map_f_eq_of_map_of_eq {i : ι} {y z : ProjectionMonoid (A i)}
    (h : ProjectionMonoid.map (ofClass (of A f i)) y =
      ProjectionMonoid.map (ofClass (of A f i)) z) :
    ∃ j, ∃ hij : i ≤ j, ProjectionMonoid.map (ofClass (f i j hij)) y =
      ProjectionMonoid.map (ofClass (f i j hij)) z := by
  induction y using ProjectionMonoid.ind with | mk a p hp => ?_
  induction z using ProjectionMonoid.ind with | mk b q hq => ?_
  rw [ProjectionMonoid.map_mk, ProjectionMonoid.map_mk, ProjectionMonoid.mk_eq_mk_iff] at h
  obtain ⟨j, hij, hj⟩ := exists_isMurrayVonNeumannEquivalent_map_f hp hq h
  refine ⟨j, hij, ?_⟩
  rw [ProjectionMonoid.map_mk, ProjectionMonoid.map_mk, ProjectionMonoid.mk_eq_mk_iff]
  exact hj

/-- **Continuity of `K₀`, surjectivity.** Every element of the projection `K₀`-group of the
C⋆-inductive limit is the image of an element of the projection `K₀`-group of some stage. -/
theorem exists_projectionKZero_map_of_eq (x : ProjectionKZero (CStarInductiveLimit A f)) :
    ∃ i, ∃ y : ProjectionKZero (A i), ProjectionKZero.map (ofClass (of A f i)) y = x := by
  obtain ⟨a, b, rfl⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨i₁, a', rfl⟩ := exists_projectionMonoid_map_of_eq a
  obtain ⟨i₂, b', rfl⟩ := exists_projectionMonoid_map_of_eq b
  obtain ⟨j, h₁, h₂⟩ := exists_ge_ge i₁ i₂
  refine ⟨j, Algebra.GrothendieckAddGroup.of (ProjectionMonoid.map (ofClass (f i₁ j h₁)) a') -
    Algebra.GrothendieckAddGroup.of (ProjectionMonoid.map (ofClass (f i₂ j h₂)) b'), ?_⟩
  rw [map_sub, ProjectionKZero.map_of, ProjectionKZero.map_of, projectionMonoid_map_of_map_f,
    projectionMonoid_map_of_map_f]

/-- **Continuity of `K₀`, injectivity.** An element of the projection `K₀`-group of a stage
that vanishes in the C⋆-inductive limit vanishes in some later stage. -/
theorem exists_projectionKZero_map_f_eq_zero_of_map_of_eq_zero {i : ι}
    {y : ProjectionKZero (A i)} (h : ProjectionKZero.map (ofClass (of A f i)) y = 0) :
    ∃ j, ∃ hij : i ≤ j, ProjectionKZero.map (ofClass (f i j hij)) y = 0 := by
  obtain ⟨a, b, rfl⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of y
  rw [map_sub, sub_eq_zero, ProjectionKZero.map_of, ProjectionKZero.map_of,
    Algebra.GrothendieckAddGroup.of_eq_of_iff] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨k, c', rfl⟩ := exists_projectionMonoid_map_of_eq c
  obtain ⟨l, hil, hkl⟩ := exists_ge_ge i k
  set a' := ProjectionMonoid.map (ofClass (f i l hil)) a
  set b' := ProjectionMonoid.map (ofClass (f i l hil)) b
  set c'' := ProjectionMonoid.map (ofClass (f k l hkl)) c'
  have hl : ProjectionMonoid.map (ofClass (of A f l)) (a' + c'') =
      ProjectionMonoid.map (ofClass (of A f l)) (b' + c'') := by
    simp only [a', b', c'', map_add, projectionMonoid_map_of_map_f]
    exact hc
  obtain ⟨j, hlj, hj⟩ := exists_projectionMonoid_map_f_eq_of_map_of_eq hl
  refine ⟨j, hil.trans hlj, ?_⟩
  rw [map_sub, sub_eq_zero, ProjectionKZero.map_of, ProjectionKZero.map_of,
    Algebra.GrothendieckAddGroup.of_eq_of_iff]
  refine ⟨ProjectionMonoid.map (ofClass (f l j hlj)) c'', ?_⟩
  simpa only [a', b', map_add, projectionMonoid_map_f_map_f] using hj

end ProjectionMonoid

end CStarInductiveLimit

end TauCeti
