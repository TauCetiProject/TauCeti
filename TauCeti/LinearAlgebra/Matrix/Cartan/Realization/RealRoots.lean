/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.WeylGroup

/-!
# Real roots, real coroots, and real reflections of a Cartan realization

For a realization `R` of a generalized Cartan matrix `A` over a field `K` of characteristic zero,
the **real roots** `Φ^re` (`TauCeti.CartanRealization.realRoots`) are the Weyl-group transforms
`w • αᵢ` of the simple roots, and the **positive real roots** `Φ₊^re` (`posRealRoots`) are those
lying in the positive root cone `Q₊`.

Following Kac, *Infinite-dimensional Lie algebras*, §3.10 and §5.1, we establish:

* **sign dichotomy** (`mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots`): every real root
  lies either in `Q₊` or in `-Q₊`;
* **reducedness** (`eq_one_or_neg_one_of_smul_mem_realRoots`, Kac Proposition 5.1(b)): the only
  scalar multiples of a real root `α` in `Φ^re` are `α` and `-α`;
* **Kac, Lemma 3.10** (`bijOn_simpleReflection_posRealRoots_diff`): each simple reflection `sᵢ`
  permutes `Φ₊^re \ {αᵢ}`;
* **well-definedness of real coroots** (`corootEquiv_smul_coroot_eq_of_smul_root_eq`, `realCoroot`,
  `realCoroot_smul`): if `w₁ • α_{i₁} = w₂ • α_{i₂}`, then `w₁ • h_{i₁} = w₂ • h_{i₂}`, so
  `(w • α)^∨ = w • α^∨` is independent of the choice of Weyl group element or simple root;
* **reflections in real roots** (`realReflection`, `weylRealReflection`,
  `isReflection_weylRealReflection`): `s_α(λ) = λ - λ(α^∨) • α` is defined on `R.realRoots hA` only
  (never on imaginary roots), belongs to the Weyl group, and is a Coxeter reflection in
  `R.weylCoxeterSystem hA`.

## Main definitions

* `TauCeti.CartanRealization.realRoots`, `posRealRoots`: real roots `Φ^re` and positive real roots
  `Φ₊^re = Φ^re ∩ Q₊`.
* `TauCeti.CartanRealization.realCoroot`: the real coroot `α^∨ ∈ H` of `α ∈ R.realRoots hA`.
* `TauCeti.CartanRealization.realReflection`, `weylRealReflection`: the reflection `s_α` on
  `Dual K H` and as an element of `R.weylGroup hA.cast_diag`.

## Main results

* `TauCeti.CartanRealization.mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots`: sign
  dichotomy on `Φ^re`.
* `TauCeti.CartanRealization.eq_one_or_neg_one_of_smul_mem_realRoots`: Kac, Proposition 5.1(b).
* `TauCeti.CartanRealization.bijOn_simpleReflection_posRealRoots_diff`: Kac, Lemma 3.10 on `Φ₊^re`.
* `TauCeti.CartanRealization.realCoroot_smul`: `(w • α)^∨ = w • α^∨`.
* `TauCeti.CartanRealization.isReflection_weylRealReflection`: every `s_α` is a Coxeter reflection.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.10 and §5.1 (Proposition 5.1).
* S. Kumar, *Kac-Moody Groups, their Flag Varieties and Representation Theory*, Progress in
  Mathematics 204, Birkhäuser, 2002, §1.3.
-/

public section

open Module

namespace TauCeti.CartanRealization

/-! ### Real roots and positive real roots over an arbitrary field -/

section Field

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (hA : A.IsGeneralizedCartan)

/-- The **real roots** `Φ^re` of a realization: the Weyl-group orbit of the simple roots in
`Dual K H`. -/
def realRoots : Set (Dual K H) :=
  {α | ∃ (w : R.weylGroup hA.cast_diag) (i : I), w • R.root i = α}

theorem realRoots_def :
    R.realRoots hA = {α | ∃ (w : R.weylGroup hA.cast_diag) (i : I), w • R.root i = α} :=
  (rfl)

theorem mem_realRoots_iff {α : Dual K H} :
    α ∈ R.realRoots hA ↔ ∃ (w : R.weylGroup hA.cast_diag) (i : I), w • R.root i = α :=
  (Iff.rfl)

/-- The **positive real roots** `Φ₊^re = Φ^re ∩ Q₊`. -/
def posRealRoots : Set (Dual K H) :=
  R.realRoots hA ∩ R.posRootCone

theorem posRealRoots_def : R.posRealRoots hA = R.realRoots hA ∩ R.posRootCone :=
  (rfl)

theorem mem_posRealRoots_iff {α : Dual K H} :
    α ∈ R.posRealRoots hA ↔ α ∈ R.realRoots hA ∧ α ∈ R.posRootCone :=
  (Iff.rfl)

theorem root_mem_realRoots (i : I) : R.root i ∈ R.realRoots hA :=
  ⟨1, i, one_smul _ _⟩

theorem root_mem_posRealRoots (i : I) : R.root i ∈ R.posRealRoots hA :=
  ⟨R.root_mem_realRoots hA i, R.root_mem_posRootCone i⟩

theorem realRoots_subset_rootLattice : R.realRoots hA ⊆ R.rootLattice := by
  rintro _ ⟨w, i, rfl⟩
  exact R.weylGroup_smul_mem_rootLattice hA.cast_diag w (R.root_mem_rootLattice i)

theorem ne_zero_of_mem_realRoots {α : Dual K H} (hα : α ∈ R.realRoots hA) : α ≠ 0 := by
  obtain ⟨w, i, rfl⟩ := hα
  intro h0
  apply R.root_linearIndependent.ne_zero i
  simpa using congrArg (w⁻¹ • ·) h0

@[simp]
theorem smul_mem_realRoots_iff (w : R.weylGroup hA.cast_diag) {α : Dual K H} :
    w • α ∈ R.realRoots hA ↔ α ∈ R.realRoots hA :=
  ⟨fun ⟨u, i, hu⟩ ↦ ⟨w⁻¹ * u, i, by rw [mul_smul, hu, inv_smul_smul]⟩,
   fun ⟨u, i, hu⟩ ↦ ⟨w * u, i, by rw [mul_smul, hu]⟩⟩

@[simp]
theorem neg_mem_realRoots_iff {α : Dual K H} :
    -α ∈ R.realRoots hA ↔ α ∈ R.realRoots hA := by
  suffices ∀ β : Dual K H, β ∈ R.realRoots hA → -β ∈ R.realRoots hA from
    ⟨fun h ↦ neg_neg α ▸ this (-α) h, this α⟩
  rintro _ ⟨w, i, rfl⟩
  exact ⟨w * R.weylSimple hA.cast_diag i, i, by simp [mul_smul]⟩

end Field

/-! ### Sign dichotomy, reducedness, real coroots, and real reflections in characteristic zero -/

section CharZero

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
  (hA : A.IsGeneralizedCartan)

/-- **Sign dichotomy for real roots**: every real root lies either in `Q₊` or in `-Q₊`. -/
theorem mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots {α : Dual K H}
    (hα : α ∈ R.realRoots hA) : α ∈ R.posRootCone ∨ -α ∈ R.posRootCone := by
  obtain ⟨w, i, rfl⟩ := hα
  rcases lt_trichotomy (R.length hA.cast_diag w)
      (R.length hA.cast_diag (w * R.weylSimple hA.cast_diag i)) with hlt | heq | hgt
  · exact Or.inl ((R.smul_root_mem_posRootCone_iff hA w i).mpr hlt)
  · exfalso
    have hne := (R.weylCoxeterSystem hA).length_mul_simple_ne w i
    simp only [weylCoxeterSystem_length, weylCoxeterSystem_simple] at hne
    exact hne heq.symm
  · exact Or.inr ((R.length_mul_weylSimple_lt_iff hA w i).mp hgt)

theorem mem_posRealRoots_or_neg_mem_posRealRoots_of_mem_realRoots {α : Dual K H}
    (hα : α ∈ R.realRoots hA) : α ∈ R.posRealRoots hA ∨ -α ∈ R.posRealRoots hA :=
  (R.mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots hA hα).imp
    (fun h ↦ ⟨hα, h⟩) (fun h ↦ ⟨(R.neg_mem_realRoots_iff hA).mpr hα, h⟩)

/-- **Kac, Proposition 5.1(b) (reducedness of real roots)**: the only scalar multiples of a real
root `α` that are real roots are `α` and `-α`. -/
theorem eq_one_or_neg_one_of_smul_mem_realRoots {α : Dual K H} (hα : α ∈ R.realRoots hA)
    {c : K} (hc : c • α ∈ R.realRoots hA) : c = 1 ∨ c = -1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact R.ne_zero_of_mem_realRoots hA hc rfl
  obtain ⟨w₁, i₁, rfl⟩ := hα
  obtain ⟨w₂, i₂, hw₂⟩ := hc
  have hmem₁ : c • R.root i₁ ∈ R.rootLattice := by
    have : c • R.root i₁ = (w₁⁻¹ * w₂) • R.root i₂ := by
      rw [mul_smul, hw₂, smul_comm, inv_smul_smul]
    rw [this]
    exact R.realRoots_subset_rootLattice hA ⟨w₁⁻¹ * w₂, i₂, rfl⟩
  have hmem₂ : c⁻¹ • R.root i₂ ∈ R.rootLattice := by
    have : c⁻¹ • R.root i₂ = (w₂⁻¹ * w₁) • R.root i₁ := by
      rw [inv_smul_eq_iff₀ hc0, mul_smul, ← smul_comm, ← hw₂, inv_smul_smul]
    rw [this]
    exact R.realRoots_subset_rootLattice hA ⟨w₂⁻¹ * w₁, i₁, rfl⟩
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp ((R.smul_root_mem_rootLattice_iff c i₁).mp hmem₁)
  obtain ⟨m, hm⟩ := Submodule.mem_one.mp ((R.smul_root_mem_rootLattice_iff c⁻¹ i₂).mp hmem₂)
  have hnm : n * m = 1 := by
    apply (algebraMap ℤ K).injective_int
    rw [map_mul, map_one, hn, hm, mul_inv_cancel₀ hc0]
  exact (Int.eq_one_or_neg_one_of_mul_eq_one hnm).imp
    (fun h ↦ by rw [← hn, h, map_one]) (fun h ↦ by rw [← hn, h, map_neg, map_one])

/-- The only natural-number multiple of a real root `α` that is a real root is `α` itself
(`n = 1`). -/
theorem eq_one_of_nsmul_mem_realRoots {α : Dual K H} (hα : α ∈ R.realRoots hA) {n : ℕ}
    (hn : (n • α : Dual K H) ∈ R.realRoots hA) : n = 1 := by
  rw [← Nat.cast_smul_eq_nsmul K] at hn
  rcases R.eq_one_or_neg_one_of_smul_mem_realRoots hA hα hn with h1 | hm1
  · exact Nat.cast_injective (R := K) (by simpa using h1)
  · exfalso
    have h0 : ((n : ℤ) : K) = ((-1 : ℤ) : K) := by
      push_cast
      exact hm1
    have := Int.cast_injective (α := K) h0
    omega

/-- **Kac, Lemma 3.10 (real roots)**: the simple reflection `sᵢ` maps every positive real root
other than `αᵢ` to a positive real root other than `αᵢ`. -/
theorem simpleReflection_mem_posRealRoots_of_ne (i : I) {α : Dual K H}
    (hα : α ∈ R.posRealRoots hA) (hne : α ≠ R.root i) :
    R.simpleReflection hA.cast_diag i α ∈ R.posRealRoots hA ∧
      R.simpleReflection hA.cast_diag i α ≠ R.root i := by
  have hs_real : R.simpleReflection hA.cast_diag i α ∈ R.realRoots hA := by
    rw [← weylSimple_smul, smul_mem_realRoots_iff]
    exact hα.1
  have hs_ne : R.simpleReflection hA.cast_diag i α ≠ R.root i := by
    intro heq
    have : α = -R.root i := by
      simpa using congrArg (R.simpleReflection hA.cast_diag i) heq
    subst this
    exact R.root_linearIndependent.ne_zero i
      (R.isPointed_posRootCone _ (R.root_mem_posRootCone i) hα.2)
  refine ⟨⟨hs_real, ?_⟩, hs_ne⟩
  rcases R.mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots hA hs_real with hpos | hneg
  · exact hpos
  exfalso
  have hα_cone : α ∈ R.posRootCone := hα.2
  rw [R.posRootCone_def, Finsupp.mem_span_range_iff_exists_finsupp] at hα_cone hneg
  obtain ⟨f, hf⟩ := hα_cone
  obtain ⟨g, hg⟩ := hneg
  have hex : ∃ j ≠ i, f j ≠ 0 := by
    by_contra! hall
    have hsupp : f = Finsupp.single i (f i) := by
      ext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [hall j hji, hji]
    rw [hsupp, Finsupp.sum_single_index (zero_smul ℕ (R.root i))] at hf
    have hfi : f i = 1 :=
      R.eq_one_of_nsmul_mem_realRoots hA (R.root_mem_realRoots hA i) (hf.symm ▸ hα.1)
    exact hne (by rw [← hf, hfi, one_smul])
  obtain ⟨j₀, hj₀, hfj₀⟩ := hex
  have hsum : α + (-R.simpleReflection hA.cast_diag i α) = α (R.coroot i) • R.root i := by
    rw [simpleReflection_apply]
    abel
  have hlin : Finsupp.linearCombination K R.root
      (f.mapRange (Nat.cast : ℕ → K) Nat.cast_zero +
        g.mapRange (Nat.cast : ℕ → K) Nat.cast_zero -
        Finsupp.single i (α (R.coroot i))) = 0 := by
    rw [map_sub, map_add, Finsupp.linearCombination_single,
      Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (fun j ↦ zero_smul K (R.root j)),
      Finsupp.sum_mapRange_index (fun j ↦ zero_smul K (R.root j))]
    simp only [Nat.cast_smul_eq_nsmul]
    rw [hf, hg, hsum, sub_self]
  have hcoeff := Finsupp.ext_iff.mp
    (linearIndependent_iff.mp R.root_linearIndependent _ hlin) j₀
  have hfg : f j₀ + g j₀ = 0 := by
    apply Nat.cast_injective (R := K)
    rw [Nat.cast_add, Nat.cast_zero]
    simpa [Finsupp.single_apply, Ne.symm hj₀] using hcoeff
  omega

/-- `sᵢ` restricts to a bijection on `Φ₊^re \ {αᵢ}`. -/
theorem bijOn_simpleReflection_posRealRoots_diff (i : I) :
    Set.BijOn (R.simpleReflection hA.cast_diag i)
      (R.posRealRoots hA \ {R.root i}) (R.posRealRoots hA \ {R.root i}) := by
  have hmaps : Set.MapsTo (R.simpleReflection hA.cast_diag i)
      (R.posRealRoots hA \ {R.root i}) (R.posRealRoots hA \ {R.root i}) :=
    fun α ⟨hα, hne⟩ ↦ R.simpleReflection_mem_posRealRoots_of_ne hA i hα hne
  refine ⟨hmaps, (R.simpleReflection hA.cast_diag i).injective.injOn, fun α hα ↦ ?_⟩
  exact ⟨R.simpleReflection hA.cast_diag i α, hmaps hα,
    R.involutive_simpleReflection hA.cast_diag i α⟩

/-! ### Well-definedness of real coroots `(wα)^∨ = w(α^∨)` and real reflections -/

/-- If `u • αᵢ = αⱼ` in the Weyl group, then `u * sᵢ * u⁻¹ = sⱼ` in `R.weylGroup hA.cast_diag`. -/
theorem conj_weylSimple_eq_of_smul_root_eq {u : R.weylGroup hA.cast_diag} {i j : I}
    (hu : u • R.root i = R.root j) :
    u * R.weylSimple hA.cast_diag i * u⁻¹ = R.weylSimple hA.cast_diag j := by
  let cs := R.weylCoxeterSystem hA
  have hnd_ui : ¬ cs.IsRightDescent u i :=
    (R.not_isRightDescent_weylCoxeterSystem_iff hA u i).mpr (hu ▸ R.root_mem_posRootCone j)
  have hu_inv : u⁻¹ • R.root j = R.root i := by rw [← hu, inv_smul_smul]
  have hnd_uj : ¬ cs.IsLeftDescent u j := by
    rw [← cs.isRightDescent_inv_iff, R.not_isRightDescent_weylCoxeterSystem_iff hA, hu_inv]
    exact R.root_mem_posRootCone i
  have hd_usi : cs.IsLeftDescent (u * cs.simple i) j := by
    rw [← cs.isRightDescent_inv_iff, mul_inv_rev, cs.inv_simple,
      R.isRightDescent_weylCoxeterSystem_iff hA, weylCoxeterSystem_simple, mul_smul, hu_inv,
      weylSimple_smul, simpleReflection_root_self, neg_neg]
    exact R.root_mem_posRootCone i
  obtain ⟨ω, hω, hprod⟩ := cs.exists_isReduced u
  have hlen_usi : cs.length (u * cs.simple i) = ω.length + 1 := by
    rw [cs.not_isRightDescent_iff.mp hnd_ui, hprod, hω.eq]
  have hred_usi : cs.IsReduced (ω ++ [i]) := by
    rw [CoxeterSystem.IsReduced, cs.wordProd_append, cs.wordProd_singleton, ← hprod, hlen_usi,
      List.length_append, List.length_singleton]
  have hprod_usi : cs.wordProd (ω ++ [i]) = u * cs.simple i := by
    rw [cs.wordProd_append, cs.wordProd_singleton, ← hprod]
  rw [← hprod_usi] at hd_usi
  obtain ⟨k, hk, hke, -⟩ := cs.exchangeCondition hred_usi hd_usi
  rw [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk_lt | rfl
  · rw [hprod_usi, List.eraseIdx_append_of_lt_length hk_lt, cs.wordProd_append,
      cs.wordProd_singleton, ← mul_assoc] at hke
    have hle := cs.length_wordProd_le (ω.eraseIdx k)
    rw [← mul_right_cancel hke, List.length_eraseIdx_of_lt hk_lt] at hle
    have hu_len : cs.length u = ω.length := by rw [hprod, hω.eq]
    exact absurd (by omega : cs.length (cs.simple j * u) < cs.length u) hnd_uj
  · rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero,
      List.append_nil, hprod_usi, ← hprod] at hke
    have h1 : cs.simple j * u * cs.simple i = u := by simpa [mul_assoc] using hke
    have h2 : cs.simple j * u = u * cs.simple i := by
      calc cs.simple j * u = cs.simple j * u * cs.simple i * cs.simple i :=
            (cs.simple_mul_simple_cancel_right i).symm
        _ = u * cs.simple i := by rw [h1]
    calc u * R.weylSimple hA.cast_diag i * u⁻¹
        = u * cs.simple i * u⁻¹ := by rw [weylCoxeterSystem_simple]
      _ = cs.simple j * u * u⁻¹ := by rw [h2]
      _ = R.weylSimple hA.cast_diag j := by
        rw [mul_assoc, mul_inv_cancel, mul_one, weylCoxeterSystem_simple]

/-- Transport of simple coroots along `W` depends only on the transported real root:
if `w₁ • α_{i₁} = w₂ • α_{i₂}`, then `w₁ • h_{i₁} = w₂ • h_{i₂}`. -/
theorem corootEquiv_smul_coroot_eq_of_smul_root_eq
    {w₁ w₂ : R.weylGroup hA.cast_diag} {i₁ i₂ : I}
    (h : w₁ • R.root i₁ = w₂ • R.root i₂) :
    R.corootEquiv hA.cast_diag w₁ • R.coroot i₁ =
      R.corootEquiv hA.cast_diag w₂ • R.coroot i₂ := by
  suffices key : ∀ (u : R.weylGroup hA.cast_diag), u • R.root i₁ = R.root i₂ →
      R.corootEquiv hA.cast_diag u • R.coroot i₁ = R.coroot i₂ by
    have hu : (w₂⁻¹ * w₁) • R.root i₁ = R.root i₂ := by
      rw [mul_smul, h, inv_smul_smul]
    have hcor := key (w₂⁻¹ * w₁) hu
    rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff] at hcor
    exact hcor
  intro u hu
  have hconj := R.conj_weylSimple_eq_of_smul_root_eq hA hu
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  have hφ : ((u * R.weylSimple hA.cast_diag i₁ * u⁻¹) • φ) = R.weylSimple hA.cast_diag i₂ • φ :=
    congrArg (· • φ) hconj
  have hcalc : (u * R.weylSimple hA.cast_diag i₁ * u⁻¹) • φ =
      φ - φ (R.corootEquiv hA.cast_diag u • R.coroot i₁) • R.root i₂ := by
    rw [mul_smul, mul_smul, weylSimple_smul, simpleReflection_apply, smul_sub, smul_inv_smul,
      smul_comm u, hu, R.weylGroup_smul_apply hA.cast_diag u⁻¹ φ (R.coroot i₁), map_inv, inv_inv]
  rw [hcalc, weylSimple_smul, simpleReflection_apply] at hφ
  have hsmul :
      (φ (R.corootEquiv hA.cast_diag u • R.coroot i₁) - φ (R.coroot i₂)) • R.root i₂ = 0 := by
    have hsub : φ (R.corootEquiv hA.cast_diag u • R.coroot i₁) • R.root i₂ =
        φ (R.coroot i₂) • R.root i₂ := by
      simpa using congrArg (φ - ·) hφ
    ext h
    simpa [sub_mul] using sub_eq_zero.mpr (congrArg (· h) hsub)
  have hscal := (smul_eq_zero.mp hsmul).resolve_right (R.root_linearIndependent.ne_zero i₂)
  simpa [map_sub] using hscal

/-- The **real coroot** `α^∨ ∈ H` attached to a real root `α ∈ R.realRoots hA`. If `α = w • αᵢ`,
then `α^∨ = w • hᵢ`, well-defined independently of `(w, i)` by
`corootEquiv_smul_coroot_eq_of_smul_root_eq`. -/
noncomputable def realCoroot (α : R.realRoots hA) : H :=
  R.corootEquiv hA.cast_diag α.2.choose • R.coroot α.2.choose_spec.choose

/-- Explicit formula for `realCoroot`: `(w • αᵢ)^∨ = w • hᵢ`. -/
theorem realCoroot_eq {α : R.realRoots hA} (w : R.weylGroup hA.cast_diag) (i : I)
    (hw : w • R.root i = α) :
    R.realCoroot hA α = R.corootEquiv hA.cast_diag w • R.coroot i :=
  R.corootEquiv_smul_coroot_eq_of_smul_root_eq hA (α.2.choose_spec.choose_spec.trans hw.symm)

@[simp]
theorem realCoroot_root (i : I) :
    R.realCoroot hA ⟨R.root i, R.root_mem_realRoots hA i⟩ = R.coroot i := by
  simpa using R.realCoroot_eq hA (α := ⟨R.root i, R.root_mem_realRoots hA i⟩) 1 i (one_smul _ _)

/-- **Equivariance of real coroots**: `(w • α)^∨ = w • α^∨` for every `w ∈ W` and `α ∈ Φ^re`. -/
@[simp]
theorem realCoroot_smul (w : R.weylGroup hA.cast_diag) (α : R.realRoots hA) :
    R.realCoroot hA ⟨w • α.1, (R.smul_mem_realRoots_iff hA w).mpr α.2⟩ =
      R.corootEquiv hA.cast_diag w • R.realCoroot hA α := by
  obtain ⟨u, i, hu⟩ := α.2
  rw [R.realCoroot_eq hA u i hu, R.realCoroot_eq hA (w * u) i (by rw [mul_smul, hu]),
    map_mul, mul_smul]

@[simp]
theorem realCoroot_neg (α : R.realRoots hA) :
    R.realCoroot hA ⟨-α.1, (R.neg_mem_realRoots_iff hA).mpr α.2⟩ = -R.realCoroot hA α := by
  obtain ⟨w, i, hw⟩ := α.2
  have hneg : (w * R.weylSimple hA.cast_diag i) • R.root i = -α.1 := by
    rw [mul_smul, weylSimple_smul, simpleReflection_root_self, smul_neg, hw]
  rw [R.realCoroot_eq hA w i hw, R.realCoroot_eq hA _ i hneg, map_mul, mul_smul,
    corootEquiv_weylSimple, corootWeylSimple_smul, simpleCoreflection_coroot_self, smul_neg]

/-- Pairing a real root with its own real coroot always equals `2`. -/
@[simp]
theorem apply_realCoroot_self (α : R.realRoots hA) :
    (α : Dual K H) (R.realCoroot hA α) = 2 := by
  obtain ⟨w, i, hw⟩ := α.2
  rw [R.realCoroot_eq hA w i hw, ← hw, weylGroup_smul_apply_corootEquiv_smul, R.root_coroot,
    hA.cast_diag i]

/-- The **reflection** `s_α : Dual K H ≃ₗ[K] Dual K H` in a real root `α ∈ Φ^re` (defined on
`R.realRoots hA` only, never on imaginary roots): `λ ↦ λ - λ(α^∨) • α`. -/
noncomputable def realReflection (α : R.realRoots hA) : Dual K H ≃ₗ[K] Dual K H :=
  Module.reflection (x := (α : Dual K H)) (f := Dual.eval K H (R.realCoroot hA α))
    (R.apply_realCoroot_self hA α)

theorem realReflection_apply (α : R.realRoots hA) (φ : Dual K H) :
    R.realReflection hA α φ = φ - φ (R.realCoroot hA α) • (α : Dual K H) :=
  Module.reflection_apply φ _

@[simp]
theorem realReflection_apply_self (α : R.realRoots hA) :
    R.realReflection hA α (α : Dual K H) = -(α : Dual K H) :=
  Module.reflection_apply_self _

theorem involutive_realReflection (α : R.realRoots hA) :
    Function.Involutive (R.realReflection hA α) :=
  Module.involutive_reflection _

@[simp]
theorem realReflection_realReflection (α : R.realRoots hA) (φ : Dual K H) :
    R.realReflection hA α (R.realReflection hA α φ) = φ :=
  R.involutive_realReflection hA α φ

@[simp]
theorem realReflection_symm (α : R.realRoots hA) :
    (R.realReflection hA α).symm = R.realReflection hA α :=
  Module.reflection_symm _

@[simp]
theorem realReflection_inv (α : R.realRoots hA) :
    (R.realReflection hA α)⁻¹ = R.realReflection hA α :=
  Module.reflection_inv _

@[simp]
theorem realReflection_mul_self (α : R.realRoots hA) :
    R.realReflection hA α * R.realReflection hA α = 1 :=
  LinearEquiv.ext (R.realReflection_realReflection hA α)

@[simp]
theorem realReflection_root (i : I) :
    R.realReflection hA ⟨R.root i, R.root_mem_realRoots hA i⟩ =
      R.simpleReflection hA.cast_diag i := by
  ext φ h
  simp [realReflection_apply, simpleReflection_apply]

@[simp]
theorem realReflection_neg (α : R.realRoots hA) :
    R.realReflection hA ⟨-α.1, (R.neg_mem_realRoots_iff hA).mpr α.2⟩ = R.realReflection hA α := by
  ext φ h
  simp [realReflection_apply]

/-- If `α = w • αᵢ`, then `s_α = w sᵢ w⁻¹` as linear automorphisms of `Dual K H`. -/
theorem realReflection_eq_conj {α : R.realRoots hA} (w : R.weylGroup hA.cast_diag) (i : I)
    (hw : w • R.root i = α) :
    R.realReflection hA α =
      (w : Dual K H ≃ₗ[K] Dual K H) * R.simpleReflection hA.cast_diag i *
        (w : Dual K H ≃ₗ[K] Dual K H)⁻¹ := by
  apply LinearEquiv.ext
  intro φ
  have hcalc : ((w * R.weylSimple hA.cast_diag i * w⁻¹ : R.weylGroup hA.cast_diag) • φ) =
      φ - φ (R.corootEquiv hA.cast_diag w • R.coroot i) • (α : Dual K H) := by
    rw [mul_smul, mul_smul, weylSimple_smul, simpleReflection_apply, smul_sub, smul_inv_smul,
      smul_comm w, hw, R.weylGroup_smul_apply hA.cast_diag w⁻¹ φ (R.coroot i), map_inv, inv_inv]
  rw [realReflection_apply, R.realCoroot_eq hA w i hw, ← hcalc, Subgroup.smul_def,
    Subgroup.coe_mul, Subgroup.coe_mul, coe_weylSimple, Subgroup.coe_inv, LinearEquiv.smul_def]

/-- Every real reflection belongs to the Weyl group. -/
theorem realReflection_mem_weylGroup (α : R.realRoots hA) :
    R.realReflection hA α ∈ R.weylGroup hA.cast_diag := by
  obtain ⟨w, i, hw⟩ := α.2
  rw [R.realReflection_eq_conj hA w i hw]
  exact mul_mem (mul_mem w.2 (R.simpleReflection_mem_weylGroup hA.cast_diag i)) (inv_mem w.2)

/-- The reflection `s_α` in a real root `α ∈ Φ^re`, as an element of `R.weylGroup hA.cast_diag`. -/
noncomputable def weylRealReflection (α : R.realRoots hA) : R.weylGroup hA.cast_diag :=
  ⟨R.realReflection hA α, R.realReflection_mem_weylGroup hA α⟩

@[simp]
theorem coe_weylRealReflection (α : R.realRoots hA) :
    (R.weylRealReflection hA α : Dual K H ≃ₗ[K] Dual K H) = R.realReflection hA α :=
  (rfl)

@[simp]
theorem weylRealReflection_smul (α : R.realRoots hA) (φ : Dual K H) :
    R.weylRealReflection hA α • φ = R.realReflection hA α φ :=
  (rfl)

@[simp]
theorem weylRealReflection_mul_self (α : R.realRoots hA) :
    R.weylRealReflection hA α * R.weylRealReflection hA α = 1 :=
  Subtype.ext (R.realReflection_mul_self hA α)

@[simp]
theorem inv_weylRealReflection (α : R.realRoots hA) :
    (R.weylRealReflection hA α)⁻¹ = R.weylRealReflection hA α :=
  Subtype.ext (R.realReflection_inv hA α)

@[simp]
theorem weylRealReflection_root (i : I) :
    R.weylRealReflection hA ⟨R.root i, R.root_mem_realRoots hA i⟩ =
      R.weylSimple hA.cast_diag i := by
  apply Subtype.ext
  rw [coe_weylRealReflection, coe_weylSimple, R.realReflection_root hA i]

@[simp]
theorem weylRealReflection_neg (α : R.realRoots hA) :
    R.weylRealReflection hA ⟨-α.1, (R.neg_mem_realRoots_iff hA).mpr α.2⟩ =
      R.weylRealReflection hA α :=
  Subtype.ext (R.realReflection_neg hA α)

theorem weylRealReflection_eq_conj {α : R.realRoots hA} (w : R.weylGroup hA.cast_diag) (i : I)
    (hw : w • R.root i = α) :
    R.weylRealReflection hA α = w * R.weylSimple hA.cast_diag i * w⁻¹ := by
  apply Subtype.ext
  rw [coe_weylRealReflection, Subgroup.coe_mul, Subgroup.coe_mul, coe_weylSimple, Subgroup.coe_inv]
  exact R.realReflection_eq_conj hA w i hw

/-- Every real reflection is a Coxeter reflection in `R.weylCoxeterSystem hA`. -/
theorem isReflection_weylRealReflection (α : R.realRoots hA) :
    (R.weylCoxeterSystem hA).IsReflection (R.weylRealReflection hA α) := by
  obtain ⟨w, i, hw⟩ := α.2
  exact ⟨w, i, by rw [weylCoxeterSystem_simple, R.weylRealReflection_eq_conj hA w i hw]⟩

end CharZero

end TauCeti.CartanRealization
