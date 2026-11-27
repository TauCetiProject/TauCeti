/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.InductiveLimit.Basic
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
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
padded to orthogonal ones of the same size; a partial isometry implementing the equivalence in
`L` is approximated from a stage and compressed between the two projections, and the resulting
approximate partial isometry becomes good enough in a later stage to give an exact equivalence
there (`IsStarProjection.exists_star_mul_self_eq_of_norm_sub_add_norm_sub_lt_one`).

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

/-- **Uniform decay.** If finitely many elements of `A i` have images of norm `< ε` in the
C⋆-inductive limit, their images in some later stage all have norm `< ε`. -/
theorem exists_forall_norm_lt {β : Type*} [Finite β] {i : ι} (a : β → A i) {ε : ℝ}
    (h : ∀ b, ‖of A f i (a b)‖ < ε) : ∃ j, ∃ hij : i ≤ j, ∀ b, ‖f i j hij (a b)‖ < ε := by
  classical
  have : Nonempty {j // i ≤ j} := ⟨⟨i, le_rfl⟩⟩
  have hb (b : β) : ∃ j, ∃ hij : i ≤ j, ‖f i j hij (a b)‖ < ε := by
    have hb := h b
    rw [norm_of] at hb
    obtain ⟨j, hj⟩ := exists_lt_of_ciInf_lt hb
    exact ⟨j, j.property, hj⟩
  choose g hg hgε using hb
  have := Fintype.ofFinite β
  obtain ⟨j, hj⟩ := Finset.exists_le (insert i (Finset.univ.image g))
  have hij : i ≤ j := hj i (Finset.mem_insert_self _ _)
  refine ⟨j, hij, fun b => ?_⟩
  have hgj : g b ≤ j :=
    hj _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  calc ‖f i j hij (a b)‖ = ‖f (g b) j hgj (f i (g b) (hg b) (a b))‖ := by
        rw [DirectedSystem.map_map (f := (f · · ·))]
    _ ≤ ‖f i (g b) (hg b) (a b)‖ := NonUnitalStarAlgHom.norm_apply_le _ _
    _ < ε := hgε b

/-- **Uniform approximation.** Finitely many elements of the C⋆-inductive limit are within `ε`
of images of elements of a common stage, which can be taken above any given index. -/
theorem exists_forall_norm_of_sub_lt {β : Type*} [Finite β] (x : β → CStarInductiveLimit A f)
    (i₀ : ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, i₀ ≤ j ∧ ∃ a : β → A j, ∀ b, ‖of A f j (a b) - x b‖ < ε := by
  classical
  have hb (b : β) : ∃ k, ∃ a : A k, ‖of A f k a - x b‖ < ε := by
    obtain ⟨y, hy, hxy⟩ := (dense_iUnion_range_of A f).exists_dist_lt (x b) hε
    obtain ⟨k, a, rfl⟩ := Set.mem_iUnion.1 hy
    exact ⟨k, a, by rwa [dist_comm, dist_eq_norm] at hxy⟩
  choose g a ha using hb
  have := Fintype.ofFinite β
  obtain ⟨j, hj⟩ := Finset.exists_le (insert i₀ (Finset.univ.image g))
  have hgj (b : β) : g b ≤ j :=
    hj _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  exact ⟨j, hj _ (Finset.mem_insert_self _ _), fun b => f (g b) j (hgj b) (a b),
    fun b => by rw [of_f]; exact ha b⟩

section Matrix

variable {N : Type*} [Fintype N]

/-- Entries of an entrywise image. -/
private theorem mapₙₐ_apply_apply {B C : Type*} [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C] (φ : B →⋆ₙₐ[ℂ] C) (M : CStarMatrix N N B) (k l : N) :
    CStarMatrix.mapₙₐ φ M k l = φ (M k l) :=
  (rfl)

/-- The canonical maps on matrices are compatible with the connecting maps. -/
private theorem mapₙₐ_of_mapₙₐ_f {i j : ι} (hij : i ≤ j) (M : CStarMatrix N N (A i)) :
    CStarMatrix.mapₙₐ (of A f j)
        (CStarMatrix.mapₙₐ (NonUnitalStarAlgHom.ofClass (f i j hij)) M) =
      CStarMatrix.mapₙₐ (of A f i) M :=
  CStarMatrix.ext fun k l => by
    simp only [mapₙₐ_apply_apply, NonUnitalStarAlgHom.coe_ofClass, of_f]

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- The connecting maps on matrices compose. -/
private theorem mapₙₐ_f_mapₙₐ_f {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (M : CStarMatrix N N (A i)) :
    CStarMatrix.mapₙₐ (NonUnitalStarAlgHom.ofClass (f j k hjk))
        (CStarMatrix.mapₙₐ (NonUnitalStarAlgHom.ofClass (f i j hij)) M) =
      CStarMatrix.mapₙₐ (NonUnitalStarAlgHom.ofClass (f i k (hij.trans hjk))) M :=
  CStarMatrix.ext fun k l => by
    simp only [mapₙₐ_apply_apply, NonUnitalStarAlgHom.coe_ofClass,
      DirectedSystem.map_map (f := (f · · ·))]

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

/-- **Defect near a projection.** If `‖x - p‖ ≤ η ≤ 1` for a star projection `p`, then
`‖x - x * x‖ ≤ 4 η`. -/
private theorem norm_sub_mul_self_le {D : Type*} [NonUnitalCStarAlgebra D] {p x : D}
    (hp : IsStarProjection p) {η : ℝ} (hx : ‖x - p‖ ≤ η) (hη : η ≤ 1) :
    ‖x - x * x‖ ≤ 4 * η := by
  set d := x - p with hd
  have he : x - x * x = d - (p * d + d * p + d * d) := by
    rw [show x = p + d by rw [hd]; abel]
    have hpp : p * p = p := hp.isIdempotentElem.eq
    noncomm_ring
    rw [hpp]
    abel
  have hp1 : ‖p‖ ≤ 1 := hp.norm_le
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hx
  rw [he]
  calc ‖d - (p * d + d * p + d * d)‖ ≤ ‖d‖ + (‖p‖ * ‖d‖ + ‖d‖ * ‖p‖ + ‖d‖ * ‖d‖) := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add₃_le).trans ?_
        gcongr <;> exact norm_mul_le _ _
    _ ≤ η + (1 * η + η * 1 + η * η) := by gcongr
    _ ≤ 4 * η := by nlinarith [norm_nonneg d]

/-- **Compressing an approximate partial isometry.** Let `v` be a partial isometry with initial
projection `p` and final projection `q`, and `‖y - v‖ ≤ η ≤ 1`. Then the compression `q y p`
has `‖(q y p)⋆ (q y p) - p‖ ≤ 3 η` and `‖(q y p) (q y p)⋆ - q‖ ≤ 3 η`. -/
private theorem norm_compress_sub_le {D : Type*} [NonUnitalCStarAlgebra D] {p q v y : D}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hv₁ : star v * v = p)
    (hv₂ : v * star v = q) (hv₃ : v * star v * v = v) {η : ℝ} (hy : ‖y - v‖ ≤ η)
    (hη : η ≤ 1) :
    ‖star (q * y * p) * (q * y * p) - p‖ ≤ 3 * η ∧
      ‖q * y * p * star (q * y * p) - q‖ ≤ 3 * η := by
  have hv1 : ‖v‖ ≤ 1 := by
    have h1 : ‖v‖ * ‖v‖ ≤ 1 := by
      rw [← CStarRing.norm_star_mul_self, hv₁]
      exact hp.norm_le
    nlinarith [norm_nonneg v]
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hy
  have hqv : q * v = v := by rw [← hv₂, hv₃]
  have hvp : v * p = v := by rw [← hv₁, ← mul_assoc, hv₃]
  set w := q * y * p
  have hwv : ‖w - v‖ ≤ η := by
    have he : q * (y - v) * p = w - v := by rw [mul_sub, sub_mul, hqv, hvp]
    rw [← he]
    calc ‖q * (y - v) * p‖ ≤ ‖q‖ * ‖y - v‖ * ‖p‖ := norm_mul₃_le
      _ ≤ 1 * η * 1 :=
        mul_le_mul (mul_le_mul hq.norm_le hy (norm_nonneg _) zero_le_one) hp.norm_le
          (norm_nonneg _) (by positivity)
      _ = η := by ring
  have hw1 : ‖w‖ ≤ 1 + η :=
    calc ‖w‖ = ‖v + (w - v)‖ := by rw [add_sub_cancel]
      _ ≤ 1 + η := norm_add_le_of_le hv1 hwv
  have key (a b c d : D) (ha : ‖a‖ ≤ 1 + η) (hb : ‖b‖ ≤ η) (hc : ‖c‖ ≤ η) (hd : ‖d‖ ≤ 1) :
      ‖a * b + c * d‖ ≤ 3 * η :=
    calc ‖a * b + c * d‖ ≤ ‖a‖ * ‖b‖ + ‖c‖ * ‖d‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (1 + η) * η + η * 1 := by gcongr
      _ ≤ 3 * η := by nlinarith
  constructor
  · have he : star w * w - p = star w * (w - v) + star (w - v) * v := by
      rw [← hv₁, star_sub]
      noncomm_ring
    rw [he]
    exact key _ _ _ _ (by rwa [norm_star]) hwv (by rwa [norm_star]) hv1
  · have he : w * star w - q = w * star (w - v) + (w - v) * star v := by
      rw [← hv₂, star_sub]
      noncomm_ring
    rw [he]
    exact key _ _ _ _ hw1 (by rwa [norm_star]) hwv (by rwa [norm_star])

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
    exact norm_sub_mul_self_le hP hXP (by linarith)
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

/-- **Approximate equivalence descends, matrix form.** If orthogonal projections `p` and `q` over
`A i` have images in the C⋆-inductive limit that are equivalent through a partial isometry `v`,
they become equivalent in some later stage. -/
private theorem exists_star_mul_self_eq_mapₙₐ_f {i : ι}
    {p q : CStarMatrix N N (A i)} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = 0) {v : CStarMatrix N N (CStarInductiveLimit A f)}
    (hv₁ : star v * v = CStarMatrix.mapₙₐ (of A f i) p)
    (hv₂ : v * star v = CStarMatrix.mapₙₐ (of A f i) q) (hv₃ : v * star v * v = v) :
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
  obtain ⟨hE₁, hE₂⟩ := norm_compress_sub_le (hp.map _) (hq.map _) hv₁ hv₂ hv₃ hYv
    (by linarith)
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
    rw [hw_def, ← mul_assoc (ψ q) (ψ q * Y), ← mul_assoc (ψ q) (ψ q), hqq,
      mul_assoc (ψ q * Y) (ψ p) (ψ p), hpp]
  have h₁ := hj true
  have h₂ := hj false
  simp only [ite_true, Bool.false_eq_true, ite_false, map_sub, map_mul, map_star] at h₁ h₂
  obtain ⟨u, hu₁, hu₂⟩ :=
    IsStarProjection.exists_star_mul_self_eq_of_norm_sub_add_norm_sub_lt_one
      ((hp.map ψ).map χ) ((hq.map ψ).map χ)
      (by rw [← map_mul, ← map_mul, hpq, map_zero, map_zero])
      (by rw [← map_mul, ← map_mul, hw']) (by linarith)
  exact ⟨j, hik.trans hkj, u, by rw [hu₁, hχψ], by rw [hu₂, hχψ]⟩

/-- Read an equivalence in `CStarMatrix N N B` as an equivalence of ordinary matrices. -/
private theorem isMurrayVonNeumannEquivalent_of_star_mul_self_eq {B : Type*}
    [NonUnitalSemiring B] [StarRing B] {p q v : CStarMatrix N N B} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h₁ : star v * v = p) (h₂ : v * star v = q) :
    IsMurrayVonNeumannEquivalent (CStarMatrix.ofMatrix.symm p) (CStarMatrix.ofMatrix.symm q) :=
  ⟨CStarMatrix.isStarProjection_ofMatrix_symm_iff.2 hp,
    CStarMatrix.isStarProjection_ofMatrix_symm_iff.2 hq, CStarMatrix.ofMatrix.symm v,
    by rw [← CStarMatrix.ofMatrix_symm_star, ← CStarMatrix.ofMatrix_symm_mul, h₁],
    by rw [← CStarMatrix.ofMatrix_symm_star, ← CStarMatrix.ofMatrix_symm_mul, h₂]⟩

/-- An entrywise image read as a C⋆-matrix. -/
private theorem ofMatrix_map {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    (φ : B →⋆ₙₐ[ℂ] C) (M : Matrix N N B) :
    CStarMatrix.ofMatrix (M.map φ) = CStarMatrix.mapₙₐ φ (CStarMatrix.ofMatrix M) :=
  (rfl)

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
  simpa using isMurrayVonNeumannEquivalent_of_star_mul_self_eq hφp hP' hv₁ hv₂

/-- **Equivalence descends, orthogonal case.** If orthogonal matrix projections `p` and `q` over
`A i` have Murray–von Neumann equivalent images in the C⋆-inductive limit, their images in some
later stage are equivalent. -/
private theorem exists_isMurrayVonNeumannEquivalent_map_f_of_mul_eq_zero {i : ι}
    {p q : Matrix N N (A i)}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0)
    (h : IsMurrayVonNeumannEquivalent (p.map (of A f i)) (q.map (of A f i))) :
    ∃ j, ∃ hij : i ≤ j,
      IsMurrayVonNeumannEquivalent (p.map (f i j hij)) (q.map (f i j hij)) := by
  classical
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := h.exists_mul_conjTranspose_mul_self_eq
  have hp' : IsStarProjection (CStarMatrix.ofMatrix p) :=
    CStarMatrix.isStarProjection_ofMatrix_iff.2 hp
  have hq' : IsStarProjection (CStarMatrix.ofMatrix q) :=
    CStarMatrix.isStarProjection_ofMatrix_iff.2 hq
  obtain ⟨j, hij, u, hu₁, hu₂⟩ := exists_star_mul_self_eq_mapₙₐ_f hp' hq'
    (v := CStarMatrix.ofMatrix v) (congrArg CStarMatrix.ofMatrix hpq)
    (by rw [← ofMatrix_map, ← hv₁]; rfl) (by rw [← ofMatrix_map, ← hv₂]; rfl)
    (congrArg CStarMatrix.ofMatrix hv₃)
  refine ⟨j, hij, ?_⟩
  simpa using isMurrayVonNeumannEquivalent_of_star_mul_self_eq (hp'.map _) (hq'.map _) hu₁ hu₂

/-- Padding to orthogonal projections: `p ⊕ 0 ∼ 0 ⊕ q` exactly when `p ∼ q`. -/
private theorem isMurrayVonNeumannEquivalent_fromBlocks_iff {B : Type*} [NonUnitalSemiring B]
    [StarRing B] {m n : Type*} [Fintype m] [Fintype n] {p : Matrix m m B} {q : Matrix n n B}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsMurrayVonNeumannEquivalent (fromBlocks p 0 0 (0 : Matrix n n B))
        (fromBlocks (0 : Matrix m m B) 0 0 q) ↔ IsMurrayVonNeumannEquivalent p q :=
  ⟨fun h ↦ hp.isMurrayVonNeumannEquivalent_fromBlocks_zero.trans
      (h.trans hq.isMurrayVonNeumannEquivalent_zero_fromBlocks.symm),
    fun h ↦ hp.isMurrayVonNeumannEquivalent_fromBlocks_zero.symm.trans
      (h.trans hq.isMurrayVonNeumannEquivalent_zero_fromBlocks)⟩

/-- **Equivalence descends.** If matrix projections `p` and `q` over `A i`, of possibly different
sizes, have Murray–von Neumann equivalent images in the C⋆-inductive limit, their images in some
later stage are equivalent. -/
theorem exists_isMurrayVonNeumannEquivalent_map_f {m n : Type*} [Fintype m] [Fintype n] {i : ι}
    {p : Matrix m m (A i)} {q : Matrix n n (A i)} (hp : IsStarProjection p)
    (hq : IsStarProjection q)
    (h : IsMurrayVonNeumannEquivalent (p.map (of A f i)) (q.map (of A f i))) :
    ∃ j, ∃ hij : i ≤ j,
      IsMurrayVonNeumannEquivalent (p.map (f i j hij)) (q.map (f i j hij)) := by
  -- pad `p` and `q` to orthogonal projections of the same size
  have hP : IsStarProjection (fromBlocks p 0 0 (0 : Matrix n n (A i))) :=
    hp.fromBlocks_zero₁₂_zero₂₁ (.zero _)
  have hQ : IsStarProjection (fromBlocks (0 : Matrix m m (A i)) 0 0 q) :=
    (IsStarProjection.zero _).fromBlocks_zero₁₂_zero₂₁ hq
  have hPQ : fromBlocks p 0 0 (0 : Matrix n n (A i)) * fromBlocks (0 : Matrix m m (A i)) 0 0 q =
      0 := by
    simp [fromBlocks_multiply]
  have hmap : IsMurrayVonNeumannEquivalent
      ((fromBlocks p 0 0 (0 : Matrix n n (A i))).map (of A f i))
      ((fromBlocks (0 : Matrix m m (A i)) 0 0 q).map (of A f i)) := by
    simpa [fromBlocks_map] using
      (isMurrayVonNeumannEquivalent_fromBlocks_iff (hp.matrix_map _) (hq.matrix_map _)).2 h
  obtain ⟨j, hij, hj⟩ := exists_isMurrayVonNeumannEquivalent_map_f_of_mul_eq_zero hP hQ hPQ hmap
  refine ⟨j, hij, ?_⟩
  rw [← isMurrayVonNeumannEquivalent_fromBlocks_iff (hp.matrix_map _) (hq.matrix_map _)]
  simpa [fromBlocks_map] using hj

end Matrix

section ProjectionMonoid

open NonUnitalStarRingHom (ofClass)

/-- The maps induced on `V` by the canonical maps are compatible with the connecting maps. -/
theorem projectionMonoid_map_of_map_f {i j : ι} (hij : i ≤ j) (y : ProjectionMonoid (A i)) :
    ProjectionMonoid.map (ofClass (of A f j)) (ProjectionMonoid.map (ofClass (f i j hij)) y) =
      ProjectionMonoid.map (ofClass (of A f i)) y := by
  rw [ProjectionMonoid.map_map]
  congr 2
  ext a
  exact of_f hij a

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- The maps induced on `V` by the connecting maps compose. -/
theorem projectionMonoid_map_f_map_f {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (y : ProjectionMonoid (A i)) :
    ProjectionMonoid.map (ofClass (f j k hjk)) (ProjectionMonoid.map (ofClass (f i j hij)) y) =
      ProjectionMonoid.map (ofClass (f i k (hij.trans hjk))) y := by
  rw [ProjectionMonoid.map_map]
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
