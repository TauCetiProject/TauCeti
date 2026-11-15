/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Sequential
public import TauCeti.Topology.Algebra.Star.PointwiseLimit

/-!
# Elliott's approximate intertwining

Elliott's approximate intertwining turns maps that are mutually inverse up to approximate
unitary equivalence into a genuine isomorphism. It is the device by which classification
theorems pass from an isomorphism of invariants to an isomorphism of C⋆-algebras.

The first result, `exists_starAlgEquiv_tendsto_of_intertwining`, is the intertwining
argument for two families of maps. Let `P` be a nonempty set of star homomorphisms `A → B`
and `Q` a set of star homomorphisms `B → A`, between separable C⋆-algebras. Suppose that
every member of `P` is inverted on finite sets to within any tolerance by some member of
`Q` on the left, and every member of `Q` likewise by some member of `P`. Then there are
sequences in `P` and in `Q` converging pointwise to a star-algebra equivalence `A ≃⋆ₐ[ℂ] B`
and to its inverse. The sequences alternate between `P` and `Q`. Each map is chosen with
error `2⁻ⁿ` on a finite set holding the first dense points and the images of the previous
finite set, so consecutive maps differ by a summable amount on every dense point.

The second result, `elliott_intertwining`, applies this to the conjugates `Ad u ∘ φ` and
`Ad v ∘ ψ` of maps `φ : A → B` and `ψ : B → A` between separable unital C⋆-algebras. If
`ψ ∘ φ` and `φ ∘ ψ` are approximately unitarily equivalent to the identities, then some
star-algebra equivalence `θ : A ≃⋆ₐ[ℂ] B` is approximately unitarily equivalent to `φ`, with
`θ⁻¹` approximately unitarily equivalent to `ψ`.

The construction follows Rørdam, *Classification of Nuclear C*-Algebras*, §2.3 (Elliott's
intertwining argument), specialised to constant sequences of algebras. The isomorphism
statement is Kirchberg–Phillips, *Embedding of exact C*-algebras in the Cuntz algebra O₂*,
Lemma 0.6.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti

section Intertwining

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- A star homomorphism of C⋆-algebras is contractive, so its error at `x` is at most the
distance from `x` to `y` plus its error at `y`. -/
private lemma norm_map_sub_le (f : A →⋆ₙₐ[ℂ] B) (x y : A) (z : B) :
    ‖f x - z‖ ≤ ‖x - y‖ + ‖f y - z‖ :=
  calc ‖f x - z‖ = ‖f (x - y) + (f y - z)‖ := by rw [map_sub, sub_add_sub_cancel]
    _ ≤ ‖f (x - y)‖ + ‖f y - z‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ + ‖f y - z‖ := by grw [NonUnitalStarAlgHom.norm_apply_le f]

/-- Evaluating a sequence of star homomorphisms along a convergent sequence of points
converges to the limit at the limit point. -/
private lemma tendsto_apply_of_tendsto {f : ℕ → A →⋆ₙₐ[ℂ] B} {x : ℕ → A} {y : A} {z : B}
    (hf : Tendsto (fun n ↦ f n y) atTop (𝓝 z)) (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n ↦ f n (x n)) atTop (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hf hx ⊢
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ norm_map_sub_le (f n) (x n) y z) ?_
  simpa using hx.add hf

/-- A sequence of star homomorphisms that is pointwise Cauchy on a dense sequence converges
pointwise to a star homomorphism. -/
private lemma exists_tendsto_of_cauchySeq {f : ℕ → A →⋆ₙₐ[ℂ] B} {d : ℕ → A}
    (hd : DenseRange d) (h : ∀ k, CauchySeq fun n ↦ f n (d k)) :
    ∃ θ : A →⋆ₙₐ[ℂ] B, ∀ x, Tendsto (fun n ↦ f n x) atTop (𝓝 (θ x)) := by
  -- The maps are contractions, so being Cauchy passes from the dense sequence to every point.
  have hc (x : A) : CauchySeq fun n ↦ f n x := by
    refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
    obtain ⟨k, hk⟩ := hd.exists_dist_lt x (by positivity : 0 < ε / 3)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp (h k) (ε / 3) (by positivity)
    have hfk (m : ℕ) : dist (f m x) (f m (d k)) < ε / 3 := by
      rw [dist_eq_norm, ← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans_lt (by rwa [← dist_eq_norm])
    refine ⟨N, fun n hn ↦ ?_⟩
    calc dist (f n x) (f N x)
        ≤ dist (f n x) (f n (d k)) + dist (f n (d k)) (f N (d k)) + dist (f N (d k)) (f N x) :=
          dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
          gcongr
          · exact hfk n
          · exact hN n hn
          · rw [dist_comm]; exact hfk N
      _ = ε := by ring
  refine ⟨nonUnitalStarAlgHomOfTendsto (fun x ↦ limUnder atTop fun n ↦ f n x) f
    (tendsto_pi_nhds.mpr fun x ↦ (hc x).tendsto_limUnder), fun x ↦ ?_⟩
  rw [nonUnitalStarAlgHomOfTendsto_apply]
  exact (hc x).tendsto_limUnder

/-- A sequence whose `n`-th step is at most `2 * 2⁻ⁿ` from some index on is Cauchy. -/
private lemma cauchySeq_of_dist_succ_le {X : Type*} [PseudoMetricSpace X] {u : ℕ → X} (k : ℕ)
    (h : ∀ n, k ≤ n → dist (u n) (u (n + 1)) ≤ 2 * (1 / 2) ^ n) : CauchySeq u := by
  refine (cauchySeq_shift k).mp (cauchySeq_of_le_geometric_two (C := 4) fun n ↦ ?_)
  have hpow : (1 / 2 : ℝ) ^ (n + k) ≤ (1 / 2) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc dist (u (n + k)) (u (n + 1 + k)) = dist (u (n + k)) (u (n + k + 1)) := by
        rw [add_right_comm]
    _ ≤ 2 * (1 / 2) ^ (n + k) := h _ (by omega)
    _ ≤ 2 * (1 / 2) ^ n := by linarith
    _ = 4 / 2 / 2 ^ n := by rw [one_div_pow]; ring

/-- A sequence whose distance to `x` is less than `2⁻ⁿ` from some index on converges to `x`. -/
private lemma tendsto_of_norm_sub_lt_pow {X : Type*} [SeminormedAddCommGroup X] {u : ℕ → X}
    {x : X} (k : ℕ) (h : ∀ n, k ≤ n → ‖u n - x‖ < (1 / 2) ^ n) : Tendsto u atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _)
    ((eventually_ge_atTop k).mono fun n hn ↦ (h n hn).le)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

variable (P : Set (A →⋆ₙₐ[ℂ] B)) (Q : Set (B →⋆ₙₐ[ℂ] A))

/-- The recursive choice behind approximate intertwining, along given sequences `a` in `A`
and `b` in `B`. The map `φ n ∈ P` is followed by `ψ n ∈ Q`, accurate to `2⁻ⁿ` on `F n`, and
then by `φ (n + 1) ∈ P`, accurate to `2⁻ⁿ` on `G n`. The set `G n` holds `b 0, …, b n` and the
image of `F n` under `φ n`, and `F (n + 1)` holds `a 0, …, a (n + 1)` and the image of `G n`
under `ψ n`. -/
private lemma exists_intertwining_seq (hP : P.Nonempty)
    (hPQ : ∀ φ ∈ P, ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ ψ ∈ Q, ∀ x ∈ F, ‖ψ (φ x) - x‖ < ε)
    (hQP : ∀ ψ ∈ Q, ∀ (G : Finset B) (ε : ℝ), 0 < ε → ∃ φ ∈ P, ∀ y ∈ G, ‖φ (ψ y) - y‖ < ε)
    (a : ℕ → A) (b : ℕ → B) :
    ∃ (φ : ℕ → A →⋆ₙₐ[ℂ] B) (ψ : ℕ → B →⋆ₙₐ[ℂ] A) (F : ℕ → Finset A) (G : ℕ → Finset B),
      (∀ n, φ n ∈ P) ∧ (∀ n, ψ n ∈ Q) ∧
      (∀ n, ∀ x ∈ F n, ‖ψ n (φ n x) - x‖ < (1 / 2) ^ n) ∧
      (∀ n, ∀ y ∈ G n, ‖φ (n + 1) (ψ n y) - y‖ < (1 / 2) ^ n) ∧
      (∀ n, ∀ x ∈ F n, φ n x ∈ G n) ∧ (∀ n, ∀ y ∈ G n, ψ n y ∈ F (n + 1)) ∧
      (∀ k n, k ≤ n → a k ∈ F n) ∧ (∀ k n, k ≤ n → b k ∈ G n) := by
  classical
  have hPQ' (φ : P) (F : Finset A) (n : ℕ) :
      ∃ ψ : Q, ∀ x ∈ F, ‖(ψ : B →⋆ₙₐ[ℂ] A) ((φ : A →⋆ₙₐ[ℂ] B) x) - x‖ < (1 / 2) ^ n := by
    obtain ⟨ψ, hψ, h⟩ := hPQ φ φ.2 F ((1 / 2) ^ n) (by positivity)
    exact ⟨⟨ψ, hψ⟩, h⟩
  have hQP' (ψ : Q) (G : Finset B) (n : ℕ) :
      ∃ φ : P, ∀ y ∈ G, ‖(φ : A →⋆ₙₐ[ℂ] B) ((ψ : B →⋆ₙₐ[ℂ] A) y) - y‖ < (1 / 2) ^ n := by
    obtain ⟨φ, hφ, h⟩ := hQP ψ ψ.2 G ((1 / 2) ^ n) (by positivity)
    exact ⟨⟨φ, hφ⟩, h⟩
  choose Ψ hΨ using hPQ'
  choose Φ hΦ using hQP'
  -- The state at stage `n` is the map `φ n` with the finite set `F n`.
  let G' (n : ℕ) (s : P × Finset A) : Finset B :=
    (Finset.range (n + 1)).image b ∪ s.2.image s.1.1
  let step (n : ℕ) (s : P × Finset A) : P × Finset A :=
    (Φ (Ψ s.1 s.2 n) (G' n s) n,
      (Finset.range (n + 2)).image a ∪ (G' n s).image (Ψ s.1 s.2 n).1)
  let s (n : ℕ) : P × Finset A :=
    Nat.rec (motive := fun _ ↦ P × Finset A) (⟨hP.some, hP.some_mem⟩, {a 0}) step n
  have hs0 : (s 0).2 = {a 0} := rfl
  have hs (n : ℕ) : s (n + 1) = step n (s n) := rfl
  refine ⟨fun n ↦ (s n).1, fun n ↦ Ψ (s n).1 (s n).2 n, fun n ↦ (s n).2,
    fun n ↦ G' n (s n), fun n ↦ (s n).1.2, fun n ↦ (Ψ _ _ n).2, fun n ↦ hΨ _ _ n,
    fun n ↦ by dsimp only; rw [hs]; exact hΦ _ _ n, fun n x hx ↦ ?_, fun n y hy ↦ ?_,
    fun k n hkn ↦ ?_, fun k n hkn ↦ ?_⟩
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)
  · dsimp only
    rw [hs]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy)
  · dsimp only
    cases n with
    | zero => rw [hs0, Nat.le_zero.mp hkn]; exact Finset.mem_singleton_self _
    | succ n =>
      rw [hs]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))

/-- **Approximate intertwining** for two families of star homomorphisms between separable
C⋆-algebras. Let every map in `P` be inverted on the left, on any finite set to any tolerance,
by some map in `Q`, and every map in `Q` likewise by some map in `P`. Then a sequence in `P`
converges pointwise to a star-algebra equivalence `θ`, and a sequence in `Q` converges
pointwise to `θ.symm`. -/
theorem exists_starAlgEquiv_tendsto_of_intertwining
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] (hP : P.Nonempty)
    (hPQ : ∀ φ ∈ P, ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ ψ ∈ Q, ∀ x ∈ F, ‖ψ (φ x) - x‖ < ε)
    (hQP : ∀ ψ ∈ Q, ∀ (G : Finset B) (ε : ℝ), 0 < ε → ∃ φ ∈ P, ∀ y ∈ G, ‖φ (ψ y) - y‖ < ε) :
    ∃ (θ : A ≃⋆ₐ[ℂ] B) (φ : ℕ → A →⋆ₙₐ[ℂ] B) (ψ : ℕ → B →⋆ₙₐ[ℂ] A),
      (∀ n, φ n ∈ P) ∧ (∀ n, ψ n ∈ Q) ∧
      (∀ x, Tendsto (fun n ↦ φ n x) atTop (𝓝 (θ x))) ∧
      ∀ y, Tendsto (fun n ↦ ψ n y) atTop (𝓝 (θ.symm y)) := by
  have ha := TopologicalSpace.denseRange_denseSeq A
  have hb := TopologicalSpace.denseRange_denseSeq B
  obtain ⟨φ, ψ, F, G, hφP, hψQ, hψφ, hφψ, hφG, hψF, haF, hbG⟩ :=
    exists_intertwining_seq P Q hP hPQ hQP (TopologicalSpace.denseSeq A)
      (TopologicalSpace.denseSeq B)
  -- Consecutive maps differ by at most `2 * 2⁻ⁿ` on the finite sets.
  have hφstep (n : ℕ) (x : A) (hx : x ∈ F n) : dist (φ n x) (φ (n + 1) x) ≤ 2 * (1 / 2) ^ n := by
    have h1 := norm_map_sub_le (φ (n + 1)) x (ψ n (φ n x)) (φ n x)
    have h2 := hψφ n x hx
    have h3 := hφψ n (φ n x) (hφG n x hx)
    rw [norm_sub_rev] at h2
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  have hψstep (n : ℕ) (y : B) (hy : y ∈ G n) : dist (ψ n y) (ψ (n + 1) y) ≤ 2 * (1 / 2) ^ n := by
    have h1 := norm_map_sub_le (ψ (n + 1)) y (φ (n + 1) (ψ n y)) (ψ n y)
    have h2 := hφψ n y hy
    have h3 := hψφ (n + 1) (ψ n y) (hψF n y hy)
    rw [norm_sub_rev] at h2
    rw [pow_succ] at h3
    rw [dist_eq_norm, norm_sub_rev]
    linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
  obtain ⟨θ, hθ⟩ := exists_tendsto_of_cauchySeq ha fun k ↦
    cauchySeq_of_dist_succ_le k fun n hn ↦ hφstep n _ (haF k n hn)
  obtain ⟨θ', hθ'⟩ := exists_tendsto_of_cauchySeq hb fun k ↦
    cauchySeq_of_dist_succ_le k fun n hn ↦ hψstep n _ (hbG k n hn)
  -- The limits are mutually inverse: check on the dense sequences, where the composites
  -- converge both to the identity and to the composite of the limits.
  have hleft : Function.LeftInverse θ' θ := by
    refine congrFun (ha.equalizer (map_continuous (θ'.comp θ)) continuous_id (funext fun k ↦ ?_))
    exact tendsto_nhds_unique (tendsto_apply_of_tendsto (hθ' _) (hθ _))
      (tendsto_of_norm_sub_lt_pow k fun n hn ↦ hψφ n _ (haF k n hn))
  have hright : Function.LeftInverse θ θ' := by
    refine congrFun (hb.equalizer (map_continuous (θ.comp θ')) continuous_id (funext fun k ↦ ?_))
    exact tendsto_nhds_unique
      (tendsto_apply_of_tendsto ((hθ _).comp (tendsto_add_atTop_nat 1)) (hθ' _))
      (tendsto_of_norm_sub_lt_pow k fun n hn ↦ hφψ n _ (hbG k n hn))
  let e := StarAlgEquiv.ofBijective θ ⟨hleft.injective, hright.surjective⟩
  have he (x : A) : e x = θ x := StarAlgEquiv.ofBijective_apply _ x
  have he' (y : B) : e.symm y = θ' y := e.symm_apply_eq.mpr (by rw [he, hright])
  exact ⟨e, φ, ψ, hφP, hψQ, fun x ↦ he x ▸ hθ x, fun y ↦ he' y ▸ hθ' y⟩

end Intertwining

section Unital

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- If `ψ ∘ φ` is approximately unitarily equivalent to the identity and `ψ` is unital, then
every conjugate `Ad u ∘ φ` is inverted on the left, on any finite set to any tolerance, by
some conjugate `Ad v ∘ ψ`. -/
private lemma exists_conj_comp_inverse {φ : A →⋆ₙₐ[ℂ] B} {ψ : B →⋆ₙₐ[ℂ] A}
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A))
    (hψ : ψ 1 = 1) (f : A →⋆ₙₐ[ℂ] B)
    (hf : f ∈ Set.range fun u : unitary B ↦
      (Unitary.conjStarAlgAut ℂ B u).toNonUnitalStarAlgHom.comp φ)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ Set.range (fun v : unitary A ↦
      (Unitary.conjStarAlgAut ℂ A v).toNonUnitalStarAlgHom.comp ψ),
        ∀ x ∈ F, ‖g (f x) - x‖ < ε := by
  obtain ⟨u, rfl⟩ := hf
  let ψ₁ : B →⋆ₐ[ℂ] A :=
    { ψ with
      map_one' := hψ
      commutes' r := by simp [Algebra.algebraMap_eq_smul_one, hψ] }
  have hψ₁ : ψ₁.toNonUnitalStarAlgHom = ψ := NonUnitalStarAlgHom.ext fun _ ↦ rfl
  have hu : ApproximatelyUnitarilyEquivalent φ
      ((Unitary.conjStarAlgAut ℂ B u).toNonUnitalStarAlgHom.comp φ) :=
    .of_unitary u fun _ ↦ by simp
  have h := hu.symm.postcomp ψ₁
  rw [hψ₁] at h
  replace h := h.trans hψφ
  obtain ⟨v, hv⟩ := (approximatelyUnitarilyEquivalent_def _ _).mp h F ε hε
  exact ⟨_, ⟨v, rfl⟩, fun x hx ↦ by simpa using hv x hx⟩

/-- **Elliott's approximate intertwining.** Let `φ : A → B` and `ψ : B → A` be star
homomorphisms between separable unital C⋆-algebras with `ψ ∘ φ` approximately unitarily
equivalent to the identity of `A` and `φ ∘ ψ` approximately unitarily equivalent to the
identity of `B`, with unitaries in `A` and in `B` respectively. Then there is a star-algebra
equivalence `θ : A ≃⋆ₐ[ℂ] B` approximately unitarily equivalent to `φ` whose inverse is
approximately unitarily equivalent to `ψ`. The hypotheses force `φ` and `ψ` to be unital. -/
theorem elliott_intertwining [TopologicalSpace.SeparableSpace A]
    [TopologicalSpace.SeparableSpace B] (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] A)
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A))
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (NonUnitalStarAlgHom.id ℂ B)) :
    ∃ θ : A ≃⋆ₐ[ℂ] B, ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ ∧
      ApproximatelyUnitarilyEquivalent θ.symm.toNonUnitalStarAlgHom ψ := by
  obtain ⟨θ, f, g, hf, hg, hfθ, hgθ⟩ := exists_starAlgEquiv_tendsto_of_intertwining
    (Set.range fun u : unitary B ↦ (Unitary.conjStarAlgAut ℂ B u).toNonUnitalStarAlgHom.comp φ)
    (Set.range fun v : unitary A ↦ (Unitary.conjStarAlgAut ℂ A v).toNonUnitalStarAlgHom.comp ψ)
    (Set.range_nonempty _) (exists_conj_comp_inverse hψφ hψφ.map_one_of_comp_id)
    (exists_conj_comp_inverse hφψ hφψ.map_one_of_comp_id)
  choose u hu using hf
  choose v hv using hg
  refine ⟨θ, (ApproximatelyUnitarilyEquivalent.of_tendsto (l := atTop) u fun x ↦ ?_).symm,
    (ApproximatelyUnitarilyEquivalent.of_tendsto (l := atTop) v fun y ↦ ?_).symm⟩
  · simpa [← hu] using hfθ x
  · simpa [← hv] using hgθ y

end Unital

end TauCeti
