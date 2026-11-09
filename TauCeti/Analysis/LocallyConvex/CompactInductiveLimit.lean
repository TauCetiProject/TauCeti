/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.DualProjectiveLimit

/-!
# Inductive limits of normed spaces with compact bonding maps

Let `B₀ → B₁ → B₂ → ⋯` be a sequence of normed spaces with continuous linear bonding maps
`T j : B j → B (j + 1)`, and let `L` be a topological vector space with compatible continuous
linear maps `ι j : B j → L`, `ι (j + 1) ∘ T j = ι j`. We say that `L` is the inductive limit of
the spectrum when every `ι j` is injective, every vector of `L` lies in the range of some `ι j`,
and a linear functional on `L` is continuous as soon as its composites with all `ι j` are
continuous. The last condition holds for the final locally convex topology of the maps `ι j`, by
`TauCeti.FinalLocallyConvexTopology.continuous_iff_continuous_comp`.

Precomposition with the maps `ι j` sends a continuous functional on `L` to a compatible family of
continuous functionals on the spaces `B j`, that is, to a point of the projective limit
`TauCeti.dualProjectiveLimit T` (`TauCeti.dualProjectiveLimit.precomp`). For an inductive limit
it is bijective (`TauCeti.dualProjectiveLimit.precomp_injective`,
`TauCeti.dualProjectiveLimit.precomp_surjective`): a compatible family of functionals glues to a
functional on `L`, which is continuous by the final-topology condition.

When the bonding maps are weakly compact, in particular when they are compact, and continuous
functionals separate the points of `L`, the inductive limit is **regular**: a subset of `L` is
bounded exactly when it is the image of a bounded subset of a single space `B j`
(`TauCeti.isVonNBounded_iff_exists_subset_image_closedBall`). Indeed, evaluations at the points
of a bounded subset of `L` form a pointwise bounded family of functionals on the Fréchet space
`lim_j B j′`, and such a family consists of evaluations at a bounded subset of one space `B j`
(`TauCeti.dualProjectiveLimit.exists_forall_exists_norm_le_eval_eq`). Consequently the strong
topology on the dual of `L`, the topology of uniform convergence on bounded subsets, is the
projective-limit topology, and precomposition is an isomorphism of topological vector spaces
`L′_b ≃ lim_j B j′` (`TauCeti.dualProjectiveLimit.strongDualEquiv`).

A typical example is the space of holomorphic germs along a compact subset of `ℂⁿ`, the inductive
limit of the Banach spaces of bounded holomorphic functions on a shrinking sequence of
neighbourhoods, whose restriction maps are compact by Montel's theorem.

## Main declarations

* `TauCeti.dualProjectiveLimit.precomp`: precomposition `L′ → lim_j B j′` with the maps `ι j`.
* `TauCeti.isVonNBounded_iff_exists_subset_image_closedBall`: regularity of the inductive limit.
* `TauCeti.dualProjectiveLimit.strongDualEquiv`: the strong dual of the inductive limit is the
  projective limit of the dual spaces.

## References

* H. Komatsu, *Projective and injective limits of weakly compact sequences of locally convex
  spaces*, J. Math. Soc. Japan 19 (1967), 366–383.
-/

public section

noncomputable section

open ContinuousLinearMap Filter Metric Topology

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {B : ℕ → Type*}
  [∀ n, NormedAddCommGroup (B n)] [∀ n, NormedSpace 𝕜 (B n)]
  {T : ∀ n, B n →L[𝕜] B (n + 1)}
  {L : Type*} [AddCommGroup L] [Module 𝕜 L] [TopologicalSpace L]
  {ι : ∀ n, B n →L[𝕜] L}

namespace dualProjectiveLimit

variable (ι) in
/-- Precomposition with compatible maps `ι j : B j → L` sends a continuous functional `φ` on `L`
to the point `(φ ∘ ι j)_j` of the projective limit `lim_j B j′`. -/
def precomp (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) :
    StrongDual 𝕜 L →L[𝕜] dualProjectiveLimit T where
  toFun φ := ⟨fun n ↦ φ.comp (ι n), mem_dualProjectiveLimit.2 fun n ↦ by rw [comp_assoc, hι]⟩
  map_add' φ ψ := by ext; simp
  map_smul' c φ := by ext; simp
  cont := (continuous_pi fun n ↦ (ContinuousLinearMap.precomp 𝕜 (ι n)).continuous).subtype_mk _

@[simp]
theorem precomp_apply (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) (φ : StrongDual 𝕜 L) (n : ℕ) :
    (precomp ι hι φ : ∀ n, StrongDual 𝕜 (B n)) n = φ.comp (ι n) :=
  (rfl)

/-- A continuous functional on `L` is determined by its composites with the maps `ι j` when the
ranges of these maps cover `L`. -/
theorem precomp_injective (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x) :
    Function.Injective (precomp ι hι) := by
  intro φ ψ h
  ext x
  obtain ⟨n, y, rfl⟩ := hcover x
  simpa using congr($(congr_arg (coord T n) h) y)

/-- A vector of `B j` can be moved along the bonding maps to any later stage `B k`, without
changing its image in `L` or its value under a compatible family of functionals. -/
private theorem exists_stage_eq (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (f : dualProjectiveLimit T) {j k : ℕ} (hjk : j ≤ k) (y : B j) :
    ∃ y' : B k, ι k y' = ι j y ∧
      (f : ∀ n, StrongDual 𝕜 (B n)) k y' = (f : ∀ n, StrongDual 𝕜 (B n)) j y := by
  induction k, hjk using Nat.le_induction with
  | base => exact ⟨y, rfl, rfl⟩
  | succ k _ ih =>
    obtain ⟨y', hι', hf'⟩ := ih
    exact ⟨T k y', by rw [← hι', ← hι k, coe_comp, Function.comp_apply],
      by rw [apply_succ_apply, hf']⟩

/-- For injective maps `ι j`, a compatible family of functionals takes the same value on two
vectors with the same image in `L`. -/
private theorem apply_eq_of_eq (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (f : dualProjectiveLimit T) {j k : ℕ} {y : B j}
    {y' : B k} (h : ι j y = ι k y') :
    (f : ∀ n, StrongDual 𝕜 (B n)) j y = (f : ∀ n, StrongDual 𝕜 (B n)) k y' := by
  rcases le_total j k with hjk | hkj
  · obtain ⟨z, hz, hfz⟩ := exists_stage_eq hι f hjk y
    rw [← hfz, hinj k (hz.trans h)]
  · obtain ⟨z, hz, hfz⟩ := exists_stage_eq hι f hkj y'
    rw [← hfz, hinj j (h.trans hz.symm)]

/-- Every compatible family of continuous functionals on the spaces `B j` comes from a continuous
functional on their inductive limit `L`. -/
theorem precomp_surjective (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hfinal : ∀ ψ : L →ₗ[𝕜] 𝕜, (∀ n, Continuous (ψ ∘ ι n)) → Continuous ψ) :
    Function.Surjective (precomp ι hι) := by
  intro f
  choose m y hy using hcover
  -- The functional `x ↦ f (m x) (y x)` is well defined, whatever stage represents `x`.
  have hval (x : L) {n : ℕ} (z : B n) (hz : ι n z = x) :
      (f : ∀ n, StrongDual 𝕜 (B n)) (m x) (y x) = (f : ∀ n, StrongDual 𝕜 (B n)) n z :=
    apply_eq_of_eq hι hinj f ((hy x).trans hz.symm)
  let ψ : L →ₗ[𝕜] 𝕜 :=
    { toFun x := (f : ∀ n, StrongDual 𝕜 (B n)) (m x) (y x)
      map_add' x x' := by
        obtain ⟨z, hz, hfz⟩ := exists_stage_eq hι f (le_max_left (m x) (m x')) (y x)
        obtain ⟨z', hz', hfz'⟩ := exists_stage_eq hι f (le_max_right (m x) (m x')) (y x')
        rw [hval (x + x') (z + z') (by rw [map_add, hz, hz', hy, hy]), map_add, hfz, hfz']
      map_smul' c x := by
        rw [hval (c • x) (c • y x) (by rw [map_smul, hy]), map_smul, RingHom.id_apply] }
  have hψ (n : ℕ) (z : B n) : ψ (ι n z) = (f : ∀ n, StrongDual 𝕜 (B n)) n z := hval _ z rfl
  refine ⟨⟨ψ, hfinal ψ fun n ↦ ?_⟩, ?_⟩
  · exact ((f : ∀ n, StrongDual 𝕜 (B n)) n).continuous.congr fun z ↦ (hψ n z).symm
  · ext n z
    exact hψ n z

end dualProjectiveLimit

open dualProjectiveLimit

/-- **Regularity of compact inductive limits.** Let `L` be the inductive limit of a sequence of
normed spaces `B j` with weakly compact bonding maps, in particular with compact bonding maps, and
suppose that continuous functionals separate the points of `L`. Then a subset of `L` is bounded
if and only if it lies in the image of a ball of a single space `B j`. -/
theorem isVonNBounded_iff_exists_subset_image_closedBall [SeparatingDual 𝕜 L]
    (hT : ∀ n, (T n).IsWeaklyCompact) (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n)
    (hinj : ∀ n, Function.Injective (ι n)) (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hfinal : ∀ ψ : L →ₗ[𝕜] 𝕜, (∀ n, Continuous (ψ ∘ ι n)) → Continuous ψ) {A : Set L} :
    Bornology.IsVonNBounded 𝕜 A ↔ ∃ j, ∃ R : ℝ, A ⊆ ι j '' closedBall 0 R := by
  refine ⟨fun hA ↦ ?_, fun ⟨j, R, hA⟩ ↦ ((NormedSpace.isVonNBounded_closedBall 𝕜 (B j) R).image
    (ι j)).subset hA⟩
  choose m y hy using hcover
  -- Evaluation at the points of `A` is a pointwise bounded family on `lim_j B j′`.
  have hbdd (f : dualProjectiveLimit T) :
      BddAbove (Set.range fun x : A ↦ ‖eval T (m x) (y x) f‖) := by
    obtain ⟨φ, rfl⟩ := precomp_surjective hι hinj (fun x ↦ ⟨m x, y x, hy x⟩) hfinal f
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
      ((NormedSpace.isVonNBounded_iff 𝕜).1 (hA.image φ))
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    simpa [hy] using hC _ (Set.mem_image_of_mem φ x.2)
  obtain ⟨j, R, hrep⟩ := exists_forall_exists_norm_le_eval_eq hT _ hbdd
  refine ⟨j, R, fun x hx ↦ ?_⟩
  obtain ⟨z, hz, heq⟩ := hrep ⟨x, hx⟩
  refine ⟨z, mem_closedBall_zero_iff.2 hz,
    (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).2 fun φ ↦ ?_⟩
  simpa [hy] using congr($heq (precomp ι hι φ))

namespace dualProjectiveLimit

/-- Inverse continuity of precomposition: by regularity, a bounded subset of `L` lies in the image
of a ball of some `B j`, on which a functional is controlled by its `j`-th coordinate norm. -/
private theorem continuous_symm_precomp [SeparatingDual 𝕜 L] (hT : ∀ n, (T n).IsWeaklyCompact)
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) (hinj : ∀ n, Function.Injective (ι n))
    (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hfinal : ∀ ψ : L →ₗ[𝕜] 𝕜, (∀ n, Continuous (ψ ∘ ι n)) → Continuous ψ) :
    Continuous (LinearEquiv.ofBijective (precomp ι hι).toLinearMap
      ⟨precomp_injective hι hcover, precomp_surjective hι hinj hcover hfinal⟩).symm := by
  have hbij : Function.Bijective (precomp ι hι).toLinearMap :=
    ⟨precomp_injective hι hcover, precomp_surjective hι hinj hcover hfinal⟩
  set e := LinearEquiv.ofBijective (precomp ι hι).toLinearMap hbij
  have he (f : dualProjectiveLimit T) {n : ℕ} (z : B n) :
      e.symm f (ι n z) = (f : ∀ n, StrongDual 𝕜 (B n)) n z := by
    conv_rhs =>
      rw [← LinearEquiv.apply_ofBijective_symm_apply (precomp ι hι).toLinearMap (h := hbij) f]
    rw [ContinuousLinearMap.coe_coe, precomp_apply, coe_comp, Function.comp_apply]
  refine continuous_of_continuousAt_zero e.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((ContinuousLinearMap.hasBasis_nhds_zero_of_basis (E := L) (σ := RingHom.id 𝕜)
    nhds_basis_ball).tendsto_right_iff).2 fun ⟨S, ε⟩ ⟨hS, hε⟩ ↦ ?_
  obtain ⟨j, R, hSR⟩ :=
    (isVonNBounded_iff_exists_subset_image_closedBall hT hι hinj hcover hfinal).1 hS
  have hR : 0 < |R| + 1 := by positivity
  filter_upwards [(coord T j).continuous.tendsto' 0 0 (map_zero _) (ball_mem_nhds 0
    (div_pos hε hR))] with f hf x hx
  obtain ⟨z, hz, rfl⟩ := hSR hx
  rw [Set.mem_preimage, mem_ball_zero_iff, coord_apply, lt_div_iff₀ hR] at hf
  simp only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, mem_ball_zero_iff, he]
  calc ‖(f : ∀ n, StrongDual 𝕜 (B n)) j z‖ ≤ ‖(f : ∀ n, StrongDual 𝕜 (B n)) j‖ * (|R| + 1) :=
        (le_opNorm _ z).trans (mul_le_mul_of_nonneg_left
          ((mem_closedBall_zero_iff.1 hz).trans ((le_abs_self R).trans (le_add_of_nonneg_right
            zero_le_one))) (norm_nonneg _))
    _ < ε := hf

/-- **The strong dual of a compact inductive limit.** Let `L` be the inductive limit of a sequence
of normed spaces `B j` with weakly compact bonding maps, in particular with compact bonding maps,
and suppose that continuous functionals separate the points of `L`. Then precomposition with the
maps `ι j` is an isomorphism of topological vector spaces from the strong dual `L′_b` onto the
projective limit `lim_j B j′` of the dual Banach spaces. -/
def strongDualEquiv [SeparatingDual 𝕜 L] (hT : ∀ n, (T n).IsWeaklyCompact)
    (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) (hinj : ∀ n, Function.Injective (ι n))
    (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
    (hfinal : ∀ ψ : L →ₗ[𝕜] 𝕜, (∀ n, Continuous (ψ ∘ ι n)) → Continuous ψ) :
    StrongDual 𝕜 L ≃L[𝕜] dualProjectiveLimit T where
  __ := LinearEquiv.ofBijective (precomp ι hι).toLinearMap
    ⟨precomp_injective hι hcover, precomp_surjective hι hinj hcover hfinal⟩
  continuous_toFun := (precomp ι hι).continuous
  continuous_invFun := continuous_symm_precomp hT hι hinj hcover hfinal

variable [SeparatingDual 𝕜 L] (hT : ∀ n, (T n).IsWeaklyCompact)
  (hι : ∀ n, (ι (n + 1)).comp (T n) = ι n) (hinj : ∀ n, Function.Injective (ι n))
  (hcover : ∀ x : L, ∃ n, ∃ y, ι n y = x)
  (hfinal : ∀ ψ : L →ₗ[𝕜] 𝕜, (∀ n, Continuous (ψ ∘ ι n)) → Continuous ψ)

@[simp]
theorem coe_strongDualEquiv :
    ⇑(strongDualEquiv hT hι hinj hcover hfinal) = precomp ι hι :=
  (rfl)

/-- The functional on `L` corresponding to a compatible family `f` takes the value `f j z` at
`ι j z`. -/
@[simp]
theorem strongDualEquiv_symm_apply_apply (f : dualProjectiveLimit T) {n : ℕ} (z : B n) :
    (strongDualEquiv hT hι hinj hcover hfinal).symm f (ι n z) =
      (f : ∀ n, StrongDual 𝕜 (B n)) n z := by
  conv_rhs => rw [← (strongDualEquiv hT hι hinj hcover hfinal).apply_symm_apply f]
  rw [coe_strongDualEquiv, precomp_apply, coe_comp, Function.comp_apply]

end dualProjectiveLimit

end TauCeti
