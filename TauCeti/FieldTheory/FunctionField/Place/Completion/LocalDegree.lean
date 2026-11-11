/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.Extension
import TauCeti.RingTheory.AdicCompletion.Pi

/-!
# The local degree of a completed extension of function fields

Let `P'` be a place of `F' / k'` lying over the place `P` of `F / k`, where `F'` is integral over
`F` and the residue extension `F'_{P'} / F_P` is finite, for instance because `F' / F` is finite.
The completed extension `F̂_P → F̂'_{P'}` (`TauCeti.Place.completionExtension`) is then a finite
extension of complete discretely valued fields of degree

`[F̂'_{P'} : F̂_P] = e(P' ∣ P) · f(P' ∣ P)`,

and the completed valuation ring `𝒪̂_{P'}` is a free module of the same rank over `𝒪̂_P`. Neither
separability nor perfectness is assumed, of `F' / F`, of the residue extension, or of the
constants: an inseparable residue extension is counted with its full degree. This identifies the
completion at a place as a finite extension of complete discrete valuation rings, the setting in
which integral bases, trace forms and the different of a completed extension are computed.

The proof exhibits an explicit basis. Choose `u_i ∈ 𝒪_{P'}` whose residues form a basis of
`F'_{P'}` over `F_P`, and a uniformizer `t` at `P'`. The products `u_i t ^ j` for
`0 ≤ j < e(P' ∣ P)` are linearly independent over `F̂_P`: the order at `P'` of an `F̂_P`-combination
of the `u_i` is a multiple of `e(P' ∣ P)`, so the blocks attached to different powers of `t` have
distinct orders. They span `𝒪̂_{P'}` over `𝒪̂_P`: every function regular at `P'` agrees to order
`e(P' ∣ P)` with an `𝒪_P`-combination of them, that is, they span `𝒪̂_{P'}` modulo
`𝔪̂_P 𝒪̂_{P'}`, and Nakayama's lemma over the complete ring `𝒪̂_P`
(`AdicCompletion.surjective_of_mkQ_comp_surjective`) lifts this to an exact expansion. Finally,
a power of a uniformizer of `P` carries every completed function into `𝒪̂_{P'}`, so the same
products span `F̂'_{P'}` over `F̂_P`.

The algebra structures are explicit, since different places over `P` give different completed
extensions: install `TauCeti.Place.completionExtensionAlgebra` and
`TauCeti.Place.completionIntegersExtensionAlgebra` locally. The latter is the algebra of the map
`TauCeti.Place.completionIntegersExtension` of completed valuation rings, defined beside the
completed extension.

## Main results

* `TauCeti.Place.linearIndependent_completionEmbedding_mul_pow` and
  `TauCeti.Place.span_completion_eq_top`: the products `u_i t ^ j` form a basis of `F̂'_{P'}`
  over `F̂_P`.
* `TauCeti.Place.linearIndependent_completionIntegersEmbedding_mul_pow` and
  `TauCeti.Place.span_completionIntegers_eq_top`: they form a basis of `𝒪̂_{P'}` over `𝒪̂_P`.
* `TauCeti.Place.moduleFinite_completionIntegers`, `TauCeti.Place.moduleFree_completionIntegers`
  and `TauCeti.Place.finrank_completionIntegers`: `𝒪̂_{P'}` is finite free over `𝒪̂_P` of rank
  `e(P' ∣ P) f(P' ∣ P)`.
* `TauCeti.Place.finiteDimensional_completion` and `TauCeti.Place.finrank_completion`: **the
  local degree** `[F̂'_{P'} : F̂_P] = e(P' ∣ P) f(P' ∣ P)`.

## References

* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §§2–3.
-/

public section

open IsLocalRing

namespace TauCeti.Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k' F')
  (hP : P'.restrict k F = P)


section Completion

variable {ι : Type*}

/-- A completed function regular at `P'` and vanishing there to order `e(P' ∣ P)` is a multiple of
a uniformizer of `P`: it lies in `𝔪̂_P • 𝒪̂_{P'}`. -/
private theorem mem_maximalIdeal_smul_top_of_mem_filtration {z : P'.completionPlace.integers}
    (hz : (z : P'.Completion) ∈ P'.completionPlace.filtration (ramificationIdx F P')) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    z ∈ (maximalIdeal P.completionPlace.integers • ⊤ :
      Submodule P.completionPlace.integers P'.completionPlace.integers) := by
  let := P.completionIntegersExtensionAlgebra P' hP
  obtain ⟨π, hπ0, hπ⟩ := P.exists_ne_zero_ord_eq 1
  have hπint : π ∈ P.integers := by rw [mem_integers_iff_ord_nonneg, hπ]; norm_num
  set πc := P.completionIntegersEmbedding ⟨π, hπint⟩
  have hπc0 : (πc : P.Completion) ≠ 0 := by simpa [πc] using hπ0
  have hπm : πc ∈ maximalIdeal P.completionPlace.integers := by
    rw [P.completionPlace.mem_maximalIdeal_iff_ord_pos hπc0]
    simp [πc, hπ]
  set E := P.completionExtension P' hP πc
  have hE0 : E ≠ 0 := (map_ne_zero _).mpr hπc0
  have hE : P'.completionPlace.ord E = ramificationIdx F P' := by
    simp [E, πc, ord_algebraMap_restrict k F P', hP, hπ]
  have hw : (z : P'.Completion) / E ∈ P'.completionPlace.integers := by
    rcases eq_or_ne (z : P'.Completion) 0 with h | h
    · simp [h]
    · rw [mem_integers_iff_ord_nonneg, P'.completionPlace.ord_div h hE0, hE]
      have := (P'.completionPlace.mem_filtration_iff_le_ord h).mp hz
      linarith
  have hzw : z = πc • (⟨_, hw⟩ : P'.completionPlace.integers) := by
    apply Subtype.ext
    rw [Algebra.smul_def, Subring.coe_mul, coe_algebraMap_completionIntegersExtensionAlgebra,
      mul_div_cancel₀ _ hE0]
  rw [hzw]
  exact Submodule.smul_mem_smul hπm Submodule.mem_top

/-- **The completed valuation ring is spanned by an expansion basis.** If the residues of
`u i ∈ 𝒪_{P'}` span the residue field of `P'` over that of `P`, and `t` is a uniformizer at `P'`,
then the products `u i * t ^ j` for `0 ≤ j < e(P' ∣ P)` span `𝒪̂_{P'}` over `𝒪̂_P`. Modulo
`𝔪̂_P 𝒪̂_{P'}` this is the expansion of a function to order `e(P' ∣ P)`, and the completeness of
`𝒪̂_P` lifts it to an exact expansion. -/
theorem span_completionIntegers_eq_top [Finite ι] (u : ι → P'.integers)
    (hu : Submodule.span (P'.restrict k F).ResidueField
      (Set.range fun i ↦ residue P'.integers (u i)) = ⊤)
    {t : P'.integers} (ht : P'.ord t = 1) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Submodule.span P.completionPlace.integers
      (Set.range fun p : ι × Fin (ramificationIdx F P') ↦
        P'.completionIntegersEmbedding (u p.1 * t ^ (p.2 : ℕ))) = ⊤ := by
  have := Fintype.ofFinite ι
  subst hP
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have : IsLocalHom (algebraMap (P'.restrict k F).completionPlace.integers
      P'.completionPlace.integers) := by
    rw [algebraMap_completionIntegersExtensionAlgebra]
    infer_instance
  have : IsHausdorff (maximalIdeal (P'.restrict k F).completionPlace.integers)
      P'.completionPlace.integers :=
    .of_map (map_maximalIdeal_le (algebraMap _ P'.completionPlace.integers))
  rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
  refine surjective_of_mkQ_comp_surjective
    (I := maximalIdeal (P'.restrict k F).completionPlace.integers) fun y ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨y₀, hy₀⟩ := P'.exists_filtration_sub_completionEmbedding_mem (ramificationIdx F P')
    ⟨y, P'.completionPlace.mem_filtration_zero_iff.mpr y.2⟩
  obtain ⟨c, hc⟩ := exists_sub_sum_mem_filtration k F P' u hu (y := y₀) (by simpa using ht)
    (ramificationIdx F P') (P'.mem_filtration_zero_iff.mp y₀.2)
  refine ⟨fun p ↦ (P'.restrict k F).completionIntegersEmbedding (c p.2 p.1), ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine mem_maximalIdeal_smul_top_of_mem_filtration (P'.restrict k F) P' rfl ?_
  have key : ((Fintype.linearCombination (P'.restrict k F).completionPlace.integers
      (fun p : ι × Fin (ramificationIdx F P') ↦
        P'.completionIntegersEmbedding (u p.1 * t ^ (p.2 : ℕ)))
      (fun p ↦ (P'.restrict k F).completionIntegersEmbedding (c p.2 p.1)) :
        P'.completionPlace.integers) : P'.Completion) =
      P'.completionEmbedding (∑ m ∈ Finset.range (ramificationIdx F P'),
        ∑ i, algebraMap F F' (c m i : F) * (u i : F') * (t : F') ^ m) := by
    rw [Fintype.linearCombination_apply, ← Fin.sum_univ_eq_sum_range
      (fun m ↦ ∑ i, algebraMap F F' (c m i : F) * (u i : F') * (t : F') ^ m),
      Finset.sum_comm, Fintype.sum_prod_type]
    push_cast
    simp only [map_sum, Algebra.smul_def]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp [mul_assoc, coe_algebraMap_completionIntegersExtensionAlgebra]
  push_cast
  rw [key, ← Submodule.neg_mem_iff, neg_sub]
  have := (P'.completionPlace.filtration (ramificationIdx F P')).add_mem hy₀
    ((P'.completionEmbedding_mem_filtration_iff).mpr hc)
  simpa [map_sub] using this

/-- The completed extension sends functions vanishing at `P` to functions vanishing at `P'`. -/
private theorem completionExtension_mem_filtration_one {x : P.Completion}
    (hx : x ∈ P.completionPlace.filtration 1) :
    P.completionExtension P' hP x ∈ P'.completionPlace.filtration 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  rw [P'.completionPlace.mem_filtration_iff_le_ord ((map_ne_zero _).mpr hx0),
    ord_completionExtension]
  have h1 := (P.completionPlace.mem_filtration_iff_le_ord hx0).mp hx
  have he : (1 : ℤ) ≤ ramificationIdx F P' := by exact_mod_cast ramificationIdx_pos F P'
  nlinarith

/-- Second stage of `exists_ord_sum_completion_eq_mul`: if the normalized coefficients `c i / c i₀`
are approximated modulo `filtration 1` by functions `d i` regular at the place below, whose
combination `T` with the `u i` is nonzero of order `0`, then the combination with the `c i` is
nonzero of order a multiple of `e(P' ∣ P)`. -/
private theorem exists_ord_sum_completion_eq_mul_of_approx [Fintype ι] (u : ι → P'.integers)
    (c : ι → (P'.restrict k F).Completion) {i₀ : ι} (hc₀ : c i₀ ≠ 0)
    (d : ι → (P'.restrict k F).integers)
    (hd : ∀ i, c i / c i₀ - (P'.restrict k F).completionEmbedding (d i) ∈
      (P'.restrict k F).completionPlace.filtration 1)
    (hT : P'.ord (∑ i, algebraMap F F' (d i : F) * (u i : F')) = 0)
    (hT0 : (∑ i, algebraMap F F' (d i : F) * (u i : F')) ≠ 0) :
    (∑ i, (P'.restrict k F).completionExtension P' rfl (c i) * P'.completionEmbedding (u i)) ≠
        0 ∧
      ∃ m : ℤ, P'.completionPlace.ord
        (∑ i, (P'.restrict k F).completionExtension P' rfl (c i) * P'.completionEmbedding (u i)) =
          ramificationIdx F P' * m := by
  set T := ∑ i, algebraMap F F' (d i : F) * (u i : F')
  set S := ∑ i, (P'.restrict k F).completionExtension P' rfl (c i / c i₀) *
    P'.completionEmbedding (u i)
  have hS : S - P'.completionEmbedding T ∈ P'.completionPlace.filtration 1 := by
    have : S - P'.completionEmbedding T = ∑ i, (P'.restrict k F).completionExtension P' rfl
        (c i / c i₀ - (P'.restrict k F).completionEmbedding (d i)) *
          P'.completionEmbedding (u i) := by
      simp [S, T, map_sum, sub_mul, Finset.sum_sub_distrib]
    rw [this]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    simpa using P'.completionPlace.mul_mem_filtration
      (completionExtension_mem_filtration_one (P'.restrict k F) P' rfl (hd i))
      (P'.completionPlace.mem_filtration_zero_iff.mpr (P'.completionIntegersEmbedding (u i)).2)
  have hvT : Valued.v (P'.completionEmbedding T) = 1 := by
    rw [valuation_completionEmbedding, P'.valuation_eq_exp_neg_ord hT0, hT, neg_zero,
      WithZero.exp_zero]
  have hvS : Valued.v S = 1 := by
    have hlt : Valued.v (S - P'.completionEmbedding T) < Valued.v (P'.completionEmbedding T) := by
      rw [hvT]
      simpa using P'.completionPlace.mem_filtration_one_iff.mp hS
    have := Valuation.map_add_eq_of_lt_right _ hlt
    rwa [sub_add_cancel, hvT] at this
  have hsum : ∑ i, (P'.restrict k F).completionExtension P' rfl (c i) *
      P'.completionEmbedding (u i) = (P'.restrict k F).completionExtension P' rfl (c i₀) * S := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hc₀]
  have hS0 : S ≠ 0 := by
    intro h
    rw [h, map_zero] at hvS
    exact zero_ne_one hvS
  have hE0 : (P'.restrict k F).completionExtension P' rfl (c i₀) ≠ 0 := (map_ne_zero _).mpr hc₀
  have hordS : P'.completionPlace.ord S = 0 :=
    (P'.completionPlace.ord_eq_iff_valuation_eq_exp_neg hS0).mpr <| by
      rw [completionPlace_valuation, hvS, neg_zero, WithZero.exp_zero]
  refine ⟨hsum ▸ mul_ne_zero hE0 hS0, (P'.restrict k F).completionPlace.ord (c i₀), ?_⟩
  rw [hsum, P'.completionPlace.ord_mul hE0 hS0, ord_completionExtension, hordS, add_zero]

/-- A nontrivial combination, with coefficients in the completion below, of functions `u i`
regular at `P'` with independent residues is nonzero, and its order at `P'` is a multiple of
`e(P' ∣ P)`. -/
private theorem exists_ord_sum_completion_eq_mul [Fintype ι] (u : ι → P'.integers)
    (hu : LinearIndependent (P'.restrict k F).ResidueField fun i ↦ residue P'.integers (u i))
    (c : ι → (P'.restrict k F).Completion) {i₁ : ι} (hi₁ : c i₁ ≠ 0) :
    (∑ i, (P'.restrict k F).completionExtension P' rfl (c i) * P'.completionEmbedding (u i)) ≠
        0 ∧
      ∃ m : ℤ, P'.completionPlace.ord
        (∑ i, (P'.restrict k F).completionExtension P' rfl (c i) * P'.completionEmbedding (u i)) =
          ramificationIdx F P' * m := by
  obtain ⟨i₀, hc₀, hdiv⟩ :=
    (P'.restrict k F).completionPlace.exists_ne_zero_forall_div_mem_integers c hi₁
  -- Approximate the normalized coefficients `c i / c i₀` by functions regular at the place below.
  have happrox : ∀ i, ∃ d : (P'.restrict k F).integers,
      c i / c i₀ - (P'.restrict k F).completionEmbedding d ∈
        (P'.restrict k F).completionPlace.filtration 1 := by
    intro i
    obtain ⟨d, hd⟩ := (P'.restrict k F).exists_filtration_sub_completionEmbedding_mem 1
      ⟨c i / c i₀, (P'.restrict k F).completionPlace.mem_filtration_zero_iff.mpr (hdiv i)⟩
    exact ⟨⟨d, (P'.restrict k F).mem_filtration_zero_iff.mp d.2⟩, hd⟩
  choose d hd using happrox
  have hunit : IsUnit (d i₀) := by
    have h : ((d i₀ : (P'.restrict k F).integers) : F) - 1 ∈ (P'.restrict k F).filtration 1 := by
      rw [← (P'.restrict k F).completionEmbedding_mem_filtration_iff, map_sub, map_one]
      have := ((P'.restrict k F).completionPlace.filtration 1).neg_mem (hd i₀)
      rwa [div_self hc₀, neg_sub] at this
    have hres := ((P'.restrict k F).residue_eq_iff_sub_mem_filtration_one (z := 1)).mpr
      (by simpa using h)
    rw [map_one] at hres
    by_contra hnu
    rw [(residue_eq_zero_iff _).mpr hnu] at hres
    exact zero_ne_one hres
  exact exists_ord_sum_completion_eq_mul_of_approx P' u c hc₀ d hd
    (ord_sum_eq_zero_of_isUnit k F P' u hu d hunit)
    (sum_ne_zero_of_linearIndependent_residue k F P' u hu (fun i ↦ (d i : F))
      (i₁ := i₀) (by simpa using hunit.ne_zero))

/-- The finite case of `TauCeti.Place.linearIndependent_completionEmbedding_mul_pow`. -/
private theorem linearIndependent_completionEmbedding_mul_pow_of_finite [Finite ι]
    (u : ι → P'.integers)
    (hu : LinearIndependent (P'.restrict k F).ResidueField fun i ↦ residue P'.integers (u i))
    {t : F'} (ht : P'.ord t = 1) :
    letI := P.completionExtensionAlgebra P' hP
    LinearIndependent P.Completion fun p : ι × Fin (ramificationIdx F P') ↦
      P'.completionEmbedding ((u p.1 : F') * t ^ (p.2 : ℕ)) := by
  have := Fintype.ofFinite ι
  classical
  subst hP
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  have ht0 : P'.completionEmbedding t ≠ 0 := by
    rintro h
    rw [(map_eq_zero_iff _ P'.completionEmbedding.injective).mp h, ord_zero] at ht
    exact zero_ne_one ht
  have ht' : P'.completionPlace.ord (P'.completionEmbedding t) = 1 := by simpa using ht
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hex
  obtain ⟨⟨i₁, j₁⟩, hp₁⟩ := not_forall.mp hex
  -- Group the relation by powers of the uniformizer; the blocks have distinct orders modulo `e`.
  set A : Fin (ramificationIdx F P') → P'.Completion := fun j ↦
    ∑ i, (P'.restrict k F).completionExtension P' rfl (c (i, j)) * P'.completionEmbedding (u i)
  have hkey : ∑ j, A j * P'.completionEmbedding t ^ (j : ℕ) = 0 := by
    rw [← hc, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, (P'.restrict k F).algebraMap_completionExtensionAlgebra P' rfl,
      map_mul, map_pow, mul_assoc]
  have hTord : ∀ j, A j * P'.completionEmbedding t ^ (j : ℕ) ≠ 0 →
      ∃ m : ℤ, P'.completionPlace.ord (A j * P'.completionEmbedding t ^ (j : ℕ)) =
        (ramificationIdx F P' : ℤ) * m + (j : ℕ) := by
    intro j hj
    have hAj : A j ≠ 0 := left_ne_zero_of_mul hj
    obtain ⟨i, hi⟩ : ∃ i, c (i, j) ≠ 0 := by
      by_contra! h
      exact hAj (by simp [A, h])
    obtain ⟨m, hm⟩ := (exists_ord_sum_completion_eq_mul P' u hu (fun i ↦ c (i, j)) hi).2
    exact ⟨m, by rw [P'.completionPlace.ord_mul hAj (pow_ne_zero _ ht0),
      P'.completionPlace.ord_pow, ht', mul_one, hm]⟩
  have hA₁ : A j₁ ≠ 0 :=
    (exists_ord_sum_completion_eq_mul P' u hu (fun i ↦ c (i, j₁)) hp₁).1
  exact sum_ne_zero_of_ord_eq_mul_add_natCast P'.completionPlace
    (fun j ↦ A j * P'.completionEmbedding t ^ (j : ℕ)) hTord
    (mul_ne_zero hA₁ (pow_ne_zero _ ht0)) hkey

/-- **Independence over the completed field below.** If the residues of `u i ∈ 𝒪_{P'}` are
independent over the residue field of `P`, and `t` is a uniformizer at `P'`, then the products
`u i * t ^ j` for `0 ≤ j < e(P' ∣ P)` are linearly independent over the completion of `F` at `P`
inside the completion of `F'` at `P'`. This is the completed form of
`TauCeti.Place.linearIndependent_mul_pow_of_linearIndependent_residue`. -/
theorem linearIndependent_completionEmbedding_mul_pow (u : ι → P'.integers)
    (hu : LinearIndependent (P'.restrict k F).ResidueField fun i ↦ residue P'.integers (u i))
    {t : F'} (ht : P'.ord t = 1) :
    letI := P.completionExtensionAlgebra P' hP
    LinearIndependent P.Completion fun p : ι × Fin (ramificationIdx F P') ↦
      P'.completionEmbedding ((u p.1 : F') * t ^ (p.2 : ℕ)) := by
  classical
  let _ := P.completionExtensionAlgebra P' hP
  -- A finite subfamily of products uses only finitely many of the `u i`.
  rw [linearIndependent_iff_finset_linearIndependent]
  intro S
  let I := S.image Prod.fst
  have hI := linearIndependent_completionEmbedding_mul_pow_of_finite P P' hP (fun i : I ↦ u i)
    (hu.comp Subtype.val Subtype.val_injective) ht
  let f : S → I × Fin (ramificationIdx F P') :=
    fun p ↦ (⟨p.1.1, Finset.mem_image_of_mem Prod.fst p.2⟩, p.1.2)
  exact hI.comp f fun p q h ↦ Subtype.ext <|
    congrArg (fun x : I × Fin (ramificationIdx F P') ↦ (x.1.1, x.2)) h

/-- The expansion family spans the completion of `F'` at `P'` over the completion of `F` at
`P`: a completed function becomes regular at `P'` after multiplication by a power of a
uniformizer of `P`. -/
theorem span_completion_eq_top [Finite ι] (u : ι → P'.integers)
    (hu : Submodule.span (P'.restrict k F).ResidueField
      (Set.range fun i ↦ residue P'.integers (u i)) = ⊤)
    {t : P'.integers} (ht : P'.ord t = 1) :
    letI := P.completionExtensionAlgebra P' hP
    Submodule.span P.Completion (Set.range fun p : ι × Fin (ramificationIdx F P') ↦
      P'.completionEmbedding ((u p.1 : F') * (t : F') ^ (p.2 : ℕ))) = ⊤ := by
  have := Fintype.ofFinite ι
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  rw [eq_top_iff]
  rintro x -
  obtain ⟨π, hπ0, hπ⟩ := P.exists_ne_zero_ord_eq 1
  set E := P.completionExtension P' hP (P.completionEmbedding π)
  have hE0 : E ≠ 0 := (map_ne_zero _).mpr (by simpa using hπ0)
  have hE : P'.completionPlace.ord E = ramificationIdx F P' := by
    simp [E, ord_algebraMap_restrict k F P', hP, hπ]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, x * E ^ N ∈ P'.completionPlace.integers := by
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, by simp⟩
    refine ⟨(P'.completionPlace.ord x).natAbs, ?_⟩
    rw [mem_integers_iff_ord_nonneg, P'.completionPlace.ord_mul hx (pow_ne_zero _ hE0),
      P'.completionPlace.ord_pow, hE]
    have he : (1 : ℤ) ≤ ramificationIdx F P' := by exact_mod_cast ramificationIdx_pos F P'
    rw [Int.natCast_natAbs]
    nlinarith [neg_abs_le (P'.completionPlace.ord x), abs_nonneg (P'.completionPlace.ord x)]
  have hy : (⟨_, hN⟩ : P'.completionPlace.integers) ∈ Submodule.span P.completionPlace.integers
      (Set.range fun p : ι × Fin (ramificationIdx F P') ↦
        P'.completionIntegersEmbedding (u p.1 * t ^ (p.2 : ℕ))) := by
    rw [span_completionIntegers_eq_top P P' hP u hu ht]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
  have ha' := congrArg (fun z : P'.completionPlace.integers ↦ (z : P'.Completion)) ha
  push_cast at ha'
  have hx : x = ∑ p, ((P.completionEmbedding π ^ N)⁻¹ * (a p : P.Completion)) •
      P'.completionEmbedding ((u p.1 : F') * (t : F') ^ (p.2 : ℕ)) := by
    calc x = (E ^ N)⁻¹ * (x * E ^ N) := by field_simp
      _ = _ := by
        rw [← ha', Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Algebra.smul_def, Algebra.smul_def, P.algebraMap_completionExtensionAlgebra P' hP,
          Subring.coe_mul, coe_algebraMap_completionIntegersExtensionAlgebra]
        simp [E, mul_assoc]
  rw [hx]
  exact Submodule.sum_mem _ fun p _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- The expansion family is also independent over the completed valuation ring below. -/
theorem linearIndependent_completionIntegersEmbedding_mul_pow (u : ι → P'.integers)
    (hu : LinearIndependent (P'.restrict k F).ResidueField fun i ↦ residue P'.integers (u i))
    {t : P'.integers} (ht : P'.ord t = 1) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    LinearIndependent P.completionPlace.integers fun p : ι × Fin (ramificationIdx F P') ↦
      P'.completionIntegersEmbedding (u p.1 * t ^ (p.2 : ℕ)) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have h := linearIndependent_completionEmbedding_mul_pow P P' hP u hu (t := (t : F')) ht
  rw [linearIndependent_iff'] at h ⊢
  intro S c hc p hp
  refine Subtype.ext (h S (fun p ↦ (c p : P.Completion)) ?_ p hp)
  have := congrArg (fun x : P'.completionPlace.integers ↦ (x : P'.Completion)) hc
  simpa [Algebra.smul_def, coe_algebraMap_completionIntegersExtensionAlgebra,
    algebraMap_completionExtensionAlgebra] using this

end Completion

section Degree

variable [FiniteDimensional (P'.restrict k F).ResidueField P'.ResidueField]

/-- A family of functions regular at `P'` whose residues form a basis of the residue extension,
together with a uniformizer at `P'`. -/
private theorem exists_residue_basis :
    ∃ (u : Fin (relativeDegree k F P') → P'.integers) (t : P'.integers),
      LinearIndependent (P'.restrict k F).ResidueField (fun i ↦ residue P'.integers (u i)) ∧
      Submodule.span (P'.restrict k F).ResidueField
        (Set.range fun i ↦ residue P'.integers (u i)) = ⊤ ∧ P'.ord t = 1 := by
  let bκ := Module.finBasisOfFinrankEq (P'.restrict k F).ResidueField P'.ResidueField
    (relativeDegree_def k F P').symm
  choose u hu using fun i ↦ residue_surjective (bκ i)
  obtain ⟨t, -, ht⟩ := P'.exists_ne_zero_ord_eq 1
  refine ⟨u, ⟨t, by rw [mem_integers_iff_ord_nonneg, ht]; norm_num⟩, ?_, ?_, ht⟩
  · simpa [hu] using bκ.linearIndependent
  · simp [hu]

/-- The expansion family is a basis of `𝒪̂_{P'}` over `𝒪̂_P`. -/
private theorem nonempty_basis_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Nonempty (Module.Basis (Fin (relativeDegree k F P') × Fin (ramificationIdx F P'))
      P.completionPlace.integers P'.completionPlace.integers) := by
  obtain ⟨u, t, hli, hsp, ht⟩ := exists_residue_basis (k := k) (F := F) P'
  exact ⟨letI := P.completionIntegersExtensionAlgebra P' hP
    Module.Basis.mk (linearIndependent_completionIntegersEmbedding_mul_pow P P' hP u hli ht)
      (span_completionIntegers_eq_top P P' hP u hsp ht).ge⟩

/-- The expansion family is a basis of the completion at `P'` over the completion at `P`. -/
private theorem nonempty_basis_completion :
    letI := P.completionExtensionAlgebra P' hP
    Nonempty (Module.Basis (Fin (relativeDegree k F P') × Fin (ramificationIdx F P'))
      P.Completion P'.Completion) := by
  obtain ⟨u, t, hli, hsp, ht⟩ := exists_residue_basis (k := k) (F := F) P'
  exact ⟨letI := P.completionExtensionAlgebra P' hP
    Module.Basis.mk (linearIndependent_completionEmbedding_mul_pow P P' hP u hli ht)
      (span_completion_eq_top P P' hP u hsp ht).ge⟩

/-- The completed valuation ring of `P'` is a finite module over the completed valuation ring
of `P`. -/
theorem moduleFinite_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.Finite P.completionPlace.integers P'.completionPlace.integers :=
  letI := P.completionIntegersExtensionAlgebra P' hP
  .of_basis (nonempty_basis_completionIntegers P P' hP).some

/-- The completed valuation ring of `P'` is a free module over the completed valuation ring
of `P`. -/
theorem moduleFree_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.Free P.completionPlace.integers P'.completionPlace.integers :=
  letI := P.completionIntegersExtensionAlgebra P' hP
  .of_basis (nonempty_basis_completionIntegers P P' hP).some

/-- **The rank of the completed valuation ring** is `e(P' ∣ P) f(P' ∣ P)`. -/
theorem finrank_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.finrank P.completionPlace.integers P'.completionPlace.integers =
      ramificationIdx F P' * relativeDegree k F P' :=
  letI := P.completionIntegersExtensionAlgebra P' hP
  (Module.finrank_eq_card_basis (nonempty_basis_completionIntegers P P' hP).some).trans
    (by simp [mul_comm])

/-- The completion of `F'` at `P'` is a finite extension of the completion of `F` at `P`. -/
theorem finiteDimensional_completion :
    letI := P.completionExtensionAlgebra P' hP
    FiniteDimensional P.Completion P'.Completion :=
  letI := P.completionExtensionAlgebra P' hP
  .of_basis (nonempty_basis_completion P P' hP).some

/-- **The local degree is `e f`**: the completion of `F'` at `P'` has degree
`e(P' ∣ P) f(P' ∣ P)` over the completion of `F` at `P`. -/
theorem finrank_completion :
    letI := P.completionExtensionAlgebra P' hP
    Module.finrank P.Completion P'.Completion = ramificationIdx F P' * relativeDegree k F P' :=
  letI := P.completionExtensionAlgebra P' hP
  (Module.finrank_eq_card_basis (nonempty_basis_completion P P' hP).some).trans
    (by simp [mul_comm])

end Degree

end TauCeti.Place
