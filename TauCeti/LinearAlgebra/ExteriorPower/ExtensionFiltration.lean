/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Prod.Basic

/-!
# The exterior-power extension filtration

For a submodule `N` of a module `M` over a commutative ring, the `n`th exterior power of `M`
carries a decreasing filtration `Fⁱ ⋀ⁿ M`, `i = 0, …, n + 1`: the submodule spanned by the wedges
`v₁ ∧ ⋯ ∧ vₙ` with at least `i` factors in `N`. For a short exact sequence `0 → P' → P → P'' → 0`
with `N` the image of `P'`, this is the exterior-power extension filtration of Serre. Its graded
pieces are expected to be `⋀ⁱ P' ⊗ ⋀ⁿ⁻ⁱ P''`, which is the module-level form of the sum formula
`λⁿ[P] = ∑ᵢ λⁱ[P'] λⁿ⁻ⁱ[P'']`; this file proves it for split sequences.

The filtration is the image of the wedge product: for every linear map `f : M' → M`,
`Fⁱ ⋀ⁱ⁺ʲ M` for `N = range f` is the image of `⋀ⁱ M' ⊗ ⋀ʲ M → ⋀ⁱ⁺ʲ M`, `a ⊗ b ↦ f a ∧ b`.
It starts at `F⁰ = ⋀ⁿ M`, ends at `Fⁿ⁺¹ = 0`, and is natural in `(M, N)`.

For the split sequence `0 → M → M × N → N → 0`, the filtration defined by the first factor
corresponds, under the exterior sum comparison `⋀ⁿ (M × N) ≃ ⨁ᵢ ⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N`, to the
summands of index at least `i`. Consequently the `i`th component of this comparison maps `Fⁱ`
onto `⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N` with kernel `Fⁱ⁺¹`.

## Main declarations

* `Submodule.exteriorPowerFiltration N n i`: the submodule `Fⁱ ⋀ⁿ M` spanned by the wedges with at
  least `i` factors in `N`.
* `Submodule.exteriorPowerFiltration_zero`, `Submodule.exteriorPowerFiltration_antitone` and
  `Submodule.exteriorPowerFiltration_eq_bot_of_lt`: `F⁰ = ⋀ⁿ M`, the filtration decreases, and
  `Fⁱ = 0` for `i > n`.
* `LinearMap.exteriorPowerWedge f i j`: the wedge product `⋀ⁱ M' ⊗ ⋀ʲ M → ⋀ⁱ⁺ʲ M`,
  `a ⊗ b ↦ f a ∧ b`, along a linear map `f : M' → M`.
* `Submodule.exteriorPowerFiltration_range_eq_range`: `Fⁱ ⋀ⁱ⁺ʲ M` for `N = range f` is the range
  of `f.exteriorPowerWedge i j`.
* `Submodule.map_exteriorPowerFiltration_le`: naturality in `(M, N)`.
* `TauCeti.exteriorPower.mem_exteriorPowerFiltration_range_inl_iff`: the ordered split comparison:
  for the first factor of `M × N`, `x ∈ Fⁱ` exactly when the components of
  `prodEquivTensor x` of index below `i` vanish.
* `TauCeti.exteriorPower.prodFiltrationComponent`, with `prodFiltrationComponent_surjective` and
  `ker_prodFiltrationComponent`: the `i`th component of the exterior sum comparison maps `Fⁱ`
  onto `⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N` with kernel `Fⁱ⁺¹`.

## References

* J.-P. Serre, *Groupes de Grothendieck des schémas en groupes réductifs déployés*,
  Publ. Math. IHÉS 34 (1968), §3.7.
* C. A. Weibel, *The K-book: an introduction to algebraic K-theory*, Graduate Studies in
  Mathematics 145, American Mathematical Society, 2013, Chapter II, Example 4.1.2.
-/

public section

noncomputable section

open scoped TensorProduct DirectSum

namespace LinearMap

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M']

/-- The wedge product `⋀ⁱ M' ⊗ ⋀ʲ M → ⋀ⁱ⁺ʲ M`, `a ⊗ b ↦ f a ∧ b`, along a linear map
`f : M' → M`. Its range is the `i`th step of the extension filtration of `range f`
(`Submodule.exteriorPowerFiltration_range_eq_range`). -/
def exteriorPowerWedge (f : M' →ₗ[R] M) (i j : ℕ) :
    ⋀[R]^i M' ⊗[R] ⋀[R]^j M →ₗ[R] ⋀[R]^(i + j) M :=
  TensorProduct.lift ((exteriorPower.wedge R M i j).compl₁₂ (exteriorPower.map i f) LinearMap.id)

/-- `f.exteriorPowerWedge i j` sends `a ⊗ b` to the product of `f a` and `b` in `⋀ M`. -/
@[simp]
theorem coe_exteriorPowerWedge_tmul (f : M' →ₗ[R] M) (i j : ℕ) (a : ⋀[R]^i M') (b : ⋀[R]^j M) :
    (f.exteriorPowerWedge i j (a ⊗ₜ b) : ExteriorAlgebra R M) = ExteriorAlgebra.map f a * b := by
  simp [exteriorPowerWedge]

end LinearMap

namespace Submodule

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M']

variable (N : Submodule R M)

/-- The exterior-power extension filtration `Fⁱ ⋀ⁿ M` of a submodule `N`: the submodule of `⋀ⁿ M`
spanned by the wedges `v₁ ∧ ⋯ ∧ vₙ` with at least `i` factors in `N`. It is decreasing in `i`
(`exteriorPowerFiltration_antitone`), starts at `F⁰ = ⋀ⁿ M` and vanishes for `i > n`. For
`N = range f`, `Fⁱ ⋀ⁱ⁺ʲ M` is the image of the wedge product `⋀ⁱ M' ⊗ ⋀ʲ M → ⋀ⁱ⁺ʲ M`
(`exteriorPowerFiltration_range_eq_range`). -/
def exteriorPowerFiltration (n i : ℕ) : Submodule R (⋀[R]^n M) :=
  span R (exteriorPower.ιMulti R n '' {v | ∃ s : Finset (Fin n), i ≤ s.card ∧ ∀ k ∈ s, v k ∈ N})

variable {N}

/-- A wedge of `n` vectors at least `i` of which lie in `N` belongs to `Fⁱ ⋀ⁿ M`. -/
theorem ιMulti_mem_exteriorPowerFiltration {n i : ℕ} {v : Fin n → M} {s : Finset (Fin n)}
    (hs : i ≤ s.card) (hv : ∀ k ∈ s, v k ∈ N) :
    exteriorPower.ιMulti R n v ∈ N.exteriorPowerFiltration n i :=
  subset_span ⟨v, ⟨s, hs, hv⟩, rfl⟩

/-- A submodule of `⋀ⁿ M` contains `Fⁱ ⋀ⁿ M` as soon as it contains every wedge of `n` vectors at
least `i` of which lie in `N`. -/
theorem exteriorPowerFiltration_le_iff {n i : ℕ} {P : Submodule R (⋀[R]^n M)} :
    N.exteriorPowerFiltration n i ≤ P ↔ ∀ (v : Fin n → M) (s : Finset (Fin n)),
      i ≤ s.card → (∀ k ∈ s, v k ∈ N) → exteriorPower.ιMulti R n v ∈ P := by
  refine ⟨fun h v s hs hv ↦ h (ιMulti_mem_exteriorPowerFiltration hs hv), fun h ↦ ?_⟩
  rw [exteriorPowerFiltration, span_le]
  rintro - ⟨v, ⟨s, hs, hv⟩, rfl⟩
  exact h v s hs hv

variable (N)

/-- The extension filtration starts at the whole exterior power: `F⁰ ⋀ⁿ M = ⋀ⁿ M`. -/
@[simp]
theorem exteriorPowerFiltration_zero (n : ℕ) : N.exteriorPowerFiltration n 0 = ⊤ := by
  rw [eq_top_iff, ← exteriorPower.ιMulti_span, span_le]
  rintro - ⟨v, rfl⟩
  exact ιMulti_mem_exteriorPowerFiltration (s := ∅) le_rfl (by simp)

/-- The extension filtration is decreasing: `Fʲ ⋀ⁿ M ≤ Fⁱ ⋀ⁿ M` for `i ≤ j`. -/
theorem exteriorPowerFiltration_antitone (n : ℕ) : Antitone (N.exteriorPowerFiltration n) :=
  fun _ _ hij ↦ exteriorPowerFiltration_le_iff.mpr fun _ _ hs hv ↦
    ιMulti_mem_exteriorPowerFiltration (hij.trans hs) hv

/-- A wedge of `n` vectors has at most `n` factors in `N`, so `Fⁱ ⋀ⁿ M = 0` for `i > n`. -/
theorem exteriorPowerFiltration_eq_bot_of_lt {n i : ℕ} (h : n < i) :
    N.exteriorPowerFiltration n i = ⊥ := by
  refine eq_bot_iff.mpr (exteriorPowerFiltration_le_iff.mpr fun v s hs _ ↦ ?_)
  have := s.card_le_univ
  simp only [Fintype.card_fin] at this
  omega

/-- The extension filtration is monotone in the submodule. -/
theorem exteriorPowerFiltration_mono {N N' : Submodule R M} (h : N ≤ N') (n i : ℕ) :
    N.exteriorPowerFiltration n i ≤ N'.exteriorPowerFiltration n i :=
  exteriorPowerFiltration_le_iff.mpr fun _ _ hs hv ↦
    ιMulti_mem_exteriorPowerFiltration hs fun k hk ↦ h (hv k hk)

/-- For `N = ⊤` every wedge of `n` vectors has `n` factors in `N`, so `Fⁱ ⋀ⁿ M = ⋀ⁿ M` for
`i ≤ n`. -/
theorem exteriorPowerFiltration_top {n i : ℕ} (h : i ≤ n) :
    (⊤ : Submodule R M).exteriorPowerFiltration n i = ⊤ := by
  rw [eq_top_iff, ← exteriorPower.ιMulti_span, span_le]
  rintro - ⟨v, rfl⟩
  exact ιMulti_mem_exteriorPowerFiltration (s := Finset.univ) (by simpa using h) (by simp)

/-- For `N = 0` a wedge with a factor in `N` vanishes, so `Fⁱ ⋀ⁿ M = 0` for `i > 0`. -/
theorem exteriorPowerFiltration_bot {n i : ℕ} (h : 0 < i) :
    (⊥ : Submodule R M).exteriorPowerFiltration n i = ⊥ := by
  refine eq_bot_iff.mpr (exteriorPowerFiltration_le_iff.mpr fun v s hs hv ↦ ?_)
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (h.trans_le hs)
  rw [mem_bot]
  exact AlternatingMap.map_coord_zero _ k ((mem_bot R).mp (hv k hk))

/-- Naturality of the extension filtration: a linear map `g : M → M₂` carrying `N` into `N₂`
carries `Fⁱ ⋀ⁿ M` into `Fⁱ ⋀ⁿ M₂`. -/
theorem map_exteriorPowerFiltration_le {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    {N₂ : Submodule R M₂} (g : M →ₗ[R] M₂) (hg : ∀ x ∈ N, g x ∈ N₂) (n i : ℕ) :
    (N.exteriorPowerFiltration n i).map (exteriorPower.map n g) ≤
      N₂.exteriorPowerFiltration n i := by
  rw [map_le_iff_le_comap, exteriorPowerFiltration_le_iff]
  intro v s hs hv
  rw [mem_comap, exteriorPower.map_apply_ιMulti]
  exact ιMulti_mem_exteriorPowerFiltration hs fun k hk ↦ hg _ (hv k hk)

/-! ### The extension filtration as the image of the wedge product -/

section range

open ExteriorAlgebra

/-- A family of submodules of the exterior algebra that contains `1` in index `0`, is stable under
left multiplication by every vector, and is moved up one index by left multiplication by a vector
of `N`, contains in index `i` every wedge with at least `i` factors in `N`. -/
private theorem ιMulti_mem_of_forall_ι_mul_mem (S : ℕ → Submodule R (ExteriorAlgebra R M))
    (h0 : 1 ∈ S 0) (hall : ∀ (z : M) (i : ℕ), ∀ x ∈ S i, ι R z * x ∈ S i)
    (hN : ∀ z ∈ N, ∀ (i : ℕ), ∀ x ∈ S i, ι R z * x ∈ S (i + 1)) :
    ∀ {n : ℕ} (v : Fin n → M) (s : Finset (Fin n)), (∀ k ∈ s, v k ∈ N) →
      ιMulti R n v ∈ S s.card := by
  intro n
  induction n with
  | zero =>
    intro v s _
    rw [Finset.card_eq_zero.mpr (Finset.eq_empty_of_isEmpty s), ιMulti_zero_apply]
    exact h0
  | succ n ih =>
    intro v s hv
    classical
    rw [ιMulti_succ_apply]
    set t : Finset (Fin n) := s.preimage Fin.succ (Fin.succ_injective _).injOn
    have ht : ∀ k ∈ t, Matrix.vecTail v k ∈ N := fun k hk ↦ hv _ (Finset.mem_preimage.mp hk)
    have ht' : t = ({k | k.succ ∈ s} : Finset (Fin n)) := by
      ext k
      rw [Finset.mem_preimage, Finset.mem_filter, and_iff_right (Finset.mem_univ k)]
    have hcard : s.card = (if (0 : Fin (n + 1)) ∈ s then 1 else 0) + t.card := by
      rw [ht', ← Fin.card_filter_univ_succ' (· ∈ s), Finset.filter_mem_eq_inter,
        Finset.univ_inter]
    by_cases h0s : (0 : Fin (n + 1)) ∈ s
    · rw [show s.card = t.card + 1 by simp only [h0s, ite_true] at hcard; omega]
      exact hN _ (hv 0 h0s) _ _ (ih _ t ht)
    · rw [show s.card = t.card by simp only [h0s, ite_false] at hcard; omega]
      exact hall _ _ _ (ih _ t ht)

variable (f : M' →ₗ[R] M)

/-- The submodule `f(⋀ⁱ M') · ⋀ M` of the exterior algebra of `M`. -/
private abbrev mulTop (i : ℕ) : Submodule R (ExteriorAlgebra R M) :=
  (⋀[R]^i M').map (ExteriorAlgebra.map f).toLinearMap * ⊤

private theorem one_mem_mulTop : (1 : ExteriorAlgebra R M) ∈ mulTop f 0 := by
  rw [← mul_one (1 : ExteriorAlgebra R M)]
  exact mul_mem_mul ⟨1, SetLike.GradedOne.one_mem, by simp⟩ mem_top

/-- `f(⋀ⁱ M') · ⋀ M` lies in a submodule `P` exactly when every product `f a * b` with
`a ∈ ⋀ⁱ M'` does. -/
private theorem mulTop_le_iff {i : ℕ} {P : Submodule R (ExteriorAlgebra R M)} :
    mulTop f i ≤ P ↔ ∀ a ∈ ⋀[R]^i M', ∀ b, ExteriorAlgebra.map f a * b ∈ P := by
  simp only [mulTop, Submodule.mul_le, mem_map, mem_top, forall_const, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, AlgHom.toLinearMap_apply]

private theorem ι_mul_mem_mulTop (z : M) (i : ℕ) (x : ExteriorAlgebra R M)
    (hx : x ∈ mulTop f i) : ι R z * x ∈ mulTop f i := by
  refine (mulTop_le_iff f (P := (mulTop f i).comap (LinearMap.mulLeft R (ι R z)))).mpr
    (fun a ha b ↦ ?_) hx
  rw [mem_comap, LinearMap.mulLeft_apply, ← mul_assoc,
    TauCeti.ExteriorAlgebra.mul_eq_neg_one_pow_smul_mul_of_mem
    (TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one z)
    (f.exteriorAlgebra_map_mem_exteriorPower ha), smul_mul_assoc, mul_assoc]
  exact smul_mem _ _ (mul_mem_mul ⟨a, ha, rfl⟩ mem_top)

private theorem ι_mul_mem_mulTop_succ (y : M') (i : ℕ) (x : ExteriorAlgebra R M)
    (hx : x ∈ mulTop f i) : ι R (f y) * x ∈ mulTop f (i + 1) := by
  refine (mulTop_le_iff f (P := (mulTop f (i + 1)).comap (LinearMap.mulLeft R (ι R (f y))))).mpr
    (fun a ha b ↦ ?_) hx
  rw [mem_comap, LinearMap.mulLeft_apply, ← mul_assoc, ← ExteriorAlgebra.map_apply_ι, ← map_mul]
  exact mul_mem_mul ⟨_, TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower y ha, rfl⟩ mem_top

/-- Every wedge of `n` vectors whose factors indexed by `s` lie in the range of `f` belongs to
`f(⋀ᵏ M') · ⋀ M` for `k = s.card`. -/
private theorem ιMulti_mem_mulTop {n : ℕ} (v : Fin n → M) (s : Finset (Fin n))
    (hv : ∀ k ∈ s, v k ∈ LinearMap.range f) : ιMulti R n v ∈ mulTop f s.card :=
  ιMulti_mem_of_forall_ι_mul_mem (N := LinearMap.range f) (mulTop f) (one_mem_mulTop f)
    (ι_mul_mem_mulTop f) (fun _ hz i x hx ↦ by
      obtain ⟨y, rfl⟩ := hz
      exact ι_mul_mem_mulTop_succ f y i x hx) v s hv

/-- Every wedge of `n` vectors at least `i` of which lie in the range of `f` belongs to
`f(⋀ⁱ M') · ⋀ M`. -/
private theorem ιMulti_mem_mulTop_of_le {n i : ℕ} {v : Fin n → M} {s : Finset (Fin n)}
    (hs : i ≤ s.card) (hv : ∀ k ∈ s, v k ∈ LinearMap.range f) : ιMulti R n v ∈ mulTop f i := by
  obtain ⟨t, hts, rfl⟩ := Finset.exists_subset_card_eq hs
  exact ιMulti_mem_mulTop f v t fun k hk ↦ hv k (hts hk)

/-- The degree-`(i + j)` part of an element of `f(⋀ⁱ M') · ⋀ M` is a wedge product `f a ∧ b` with
`a ∈ ⋀ⁱ M'` and `b ∈ ⋀ʲ M`. -/
private theorem proj_mem_range_of_mem_mulTop (i j : ℕ) (x : ExteriorAlgebra R M)
    (hx : x ∈ mulTop f i) :
    TauCeti.exteriorPower.proj R M (i + j) x ∈ LinearMap.range (f.exteriorPowerWedge i j) := by
  refine (mulTop_le_iff f (P := (LinearMap.range (f.exteriorPowerWedge i j)).comap
    (TauCeti.exteriorPower.proj R M (i + j)))).mpr (fun a ha b ↦ ?_) hx
  refine ⟨⟨a, ha⟩ ⊗ₜ TauCeti.exteriorPower.proj R M j b, Subtype.ext ?_⟩
  rw [LinearMap.coe_exteriorPowerWedge_tmul, TauCeti.exteriorPower.proj_apply,
    TauCeti.exteriorPower.proj_apply,
    DirectSum.coe_decompose_mul_of_left_mem_of_le (fun i ↦ ⋀[R]^i M)
      (f.exteriorAlgebra_map_mem_exteriorPower ha) (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

/-- Every wedge product `f a ∧ b` with `a ∈ ⋀ⁱ M'` and `b ∈ ⋀ʲ M` lies in `Fⁱ ⋀ⁱ⁺ʲ M` for
`N = range f`. -/
private theorem exteriorPowerWedge_tmul_mem_exteriorPowerFiltration (i j : ℕ) (a : ⋀[R]^i M')
    (b : ⋀[R]^j M) :
    f.exteriorPowerWedge i j (a ⊗ₜ b) ∈
      (LinearMap.range f).exteriorPowerFiltration (i + j) i := by
  have ha : a ∈ span R (Set.range (exteriorPower.ιMulti R i)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  have hb : b ∈ span R (Set.range (exteriorPower.ιMulti R j)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem a b ha hb =>
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨w, rfl⟩ := hb
    have : f.exteriorPowerWedge i j (exteriorPower.ιMulti R i u ⊗ₜ exteriorPower.ιMulti R j w) =
        exteriorPower.ιMulti R (i + j) (Fin.append (f ∘ u) w) :=
      Subtype.ext (by simp [ExteriorAlgebra.ιMulti_mul_ιMulti])
    rw [this]
    refine ιMulti_mem_exteriorPowerFiltration
      (s := Finset.univ.map (Fin.castAddEmb j)) (by simp) fun k hk ↦ ?_
    obtain ⟨l, -, rfl⟩ := Finset.mem_map.mp hk
    simp
  | zero_left => simp
  | zero_right => simp
  | add_left _ _ _ _ _ _ h h' => rw [TensorProduct.add_tmul, map_add]; exact add_mem h h'
  | add_right _ _ _ _ _ _ h h' => rw [TensorProduct.tmul_add, map_add]; exact add_mem h h'
  | smul_left r _ _ _ _ h => rw [← TensorProduct.smul_tmul', map_smul]; exact smul_mem _ r h
  | smul_right r _ _ _ _ h => rw [TensorProduct.tmul_smul, map_smul]; exact smul_mem _ r h

/-- The extension filtration of the range of `f : M' → M` is the image of the wedge product:
`Fⁱ ⋀ⁱ⁺ʲ M` is the image of `⋀ⁱ M' ⊗ ⋀ʲ M → ⋀ⁱ⁺ʲ M`, `a ⊗ b ↦ f a ∧ b`. -/
theorem exteriorPowerFiltration_range_eq_range (i j : ℕ) :
    (LinearMap.range f).exteriorPowerFiltration (i + j) i =
      LinearMap.range (f.exteriorPowerWedge i j) := by
  apply le_antisymm
  · rw [exteriorPowerFiltration_le_iff]
    intro v s hs hv
    have := proj_mem_range_of_mem_mulTop f i j _ (ιMulti_mem_mulTop_of_le f hs hv)
    rwa [← exteriorPower.ιMulti_apply_coe, TauCeti.exteriorPower.proj_coe] at this
  · rw [LinearMap.range_eq_map, ← TensorProduct.span_tmul_eq_top, map_span_le]
    rintro - ⟨a, b, rfl⟩
    exact exteriorPowerWedge_tmul_mem_exteriorPowerFiltration f i j a b

end range

end Submodule

/-! ### The split case -/

namespace TauCeti

namespace exteriorPower

open Submodule

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A wedge product `a ∧ b` of `a ∈ ⋀ᵖ M` and `b ∈ ⋀^q N` lies in the `p`th step of the extension
filtration of the first factor of `M × N`. -/
theorem wedgeTensor_mem_exteriorPowerFiltration (p q n : ℕ) (h : p + q = n)
    (t : ⋀[R]^p M ⊗[R] ⋀[R]^q N) :
    wedgeTensor R M N p q n h t ∈
      (LinearMap.range (LinearMap.inl R M N)).exteriorPowerFiltration n p := by
  subst h
  rw [exteriorPowerFiltration_range_eq_range]
  have hcomp : (LinearMap.inl R M N).exteriorPowerWedge p q ∘ₗ
        TensorProduct.map LinearMap.id (_root_.exteriorPower.map q (LinearMap.inr R M N)) =
      wedgeTensor R M N p q (p + q) rfl :=
    TensorProduct.ext' fun a b ↦ Subtype.ext (by simp)
  exact ⟨_, LinearMap.congr_fun hcomp t⟩

/-- In the exterior algebra of `M × N`, the bidegree-`(k, m)` component of `a ∧ y`, for
`a ∈ ⋀ᵖ M` and any `y`, vanishes when `k < p`. -/
private theorem map_proj_prodEquivTensor_map_inl_mul {p k : ℕ} (hk : k < p) (m : ℕ)
    {a : ExteriorAlgebra R M} (ha : a ∈ ⋀[R]^p M) (y : ExteriorAlgebra R (M × N)) :
    TensorProduct.map (proj R M k) (proj R N m) ((GradedTensorProduct.of R _ _).symm
      (ExteriorAlgebra.prodEquivTensor R M N
        (ExteriorAlgebra.map (LinearMap.inl R M N) a * y))) = 0 := by
  have hinl :
      ExteriorAlgebra.prodEquivTensor R M N (ExteriorAlgebra.map (LinearMap.inl R M N) a) =
        a ᵍ⊗ₜ[R] (1 : ExteriorAlgebra R N) := by
    rw [← AlgEquiv.apply_symm_apply (ExteriorAlgebra.prodEquivTensor R M N) (a ᵍ⊗ₜ[R] 1),
      ExteriorAlgebra.prodEquivTensor_symm_tmul, map_one, mul_one]
  rw [map_mul, hinl]
  generalize ExteriorAlgebra.prodEquivTensor R M N y = Y
  obtain ⟨Y, rfl⟩ := (GradedTensorProduct.of R (fun i ↦ ⋀[R]^i M) (fun i ↦ ⋀[R]^i N)).surjective Y
  induction Y using TensorProduct.inductionOn with
  | add Y Y' hY hY' => rw [map_add, mul_add, map_add, map_add, hY, hY', add_zero]
  | tmul c d =>
    induction c using DirectSum.Decomposition.inductionOn (fun i ↦ ⋀[R]^i M) with
    | zero => simp
    | add c c' hc hc' => rw [TensorProduct.add_tmul, map_add, mul_add, map_add, map_add, hc, hc',
        add_zero]
    | @homogeneous q c =>
      have hac : a * c ∈ ⋀[R]^(p + q) M := SetLike.mul_mem_graded ha c.property
      have hproj : proj R M k (a * c) = 0 :=
        Subtype.ext (by simp [coe_proj_of_mem hac, show p + q ≠ k by omega])
      rw [← GradedTensorProduct.tmul, GradedTensorProduct.tmul_one_mul_coe_tmul,
        GradedTensorProduct.tmul, GradedTensorProduct.of_symm_of, TensorProduct.map_tmul, hproj,
        TensorProduct.zero_tmul]

/-- **The ordered split comparison.** For the first factor of `M × N`, an element `x` of
`⋀ⁿ (M × N)` lies in the extension filtration `Fⁱ` exactly when the components of
`prodEquivTensor x ∈ ⨁ₖ ⋀ᵏ M ⊗ ⋀ⁿ⁻ᵏ N` of index `k < i` vanish. Thus `Fⁱ` corresponds to the
summands `⋀ᵏ M ⊗ ⋀ⁿ⁻ᵏ N` with `k ≥ i`. -/
theorem mem_exteriorPowerFiltration_range_inl_iff {n i : ℕ} {x : ⋀[R]^n (M × N)} :
    x ∈ (LinearMap.range (LinearMap.inl R M N)).exteriorPowerFiltration n i ↔
      ∀ k : Fin (n + 1), (k : ℕ) < i → prodEquivTensor R M N n x k = 0 := by
  constructor
  · intro hx k hk
    suffices (LinearMap.range (LinearMap.inl R M N)).exteriorPowerFiltration n i ≤
        LinearMap.ker (DirectSum.component R _ _ k ∘ₗ (prodEquivTensor R M N n).toLinearMap) from
      this hx
    rw [exteriorPowerFiltration_le_iff]
    intro v s hs hv
    have hmem := Submodule.ιMulti_mem_mulTop_of_le (LinearMap.inl R M N) hs hv
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ← DirectSum.apply_eq_component, prodEquivTensor_apply, _root_.exteriorPower.ιMulti_apply_coe]
    have key : Submodule.mulTop (LinearMap.inl R M N) i ≤ LinearMap.ker
        (TensorProduct.map (proj R M k) (proj R N (n - k)) ∘ₗ
          (GradedTensorProduct.of R (fun i ↦ ⋀[R]^i M) (fun i ↦ ⋀[R]^i N)).symm.toLinearMap ∘ₗ
          (ExteriorAlgebra.prodEquivTensor R M N).toLinearMap) :=
      (Submodule.mulTop_le_iff _).mpr fun a ha b ↦ map_proj_prodEquivTensor_map_inl_mul hk _ ha b
    simpa only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
      AlgEquiv.toLinearMap_apply] using key hmem
  · intro hx
    rw [← (prodEquivTensor R M N n).symm_apply_apply x,
      ← DirectSum.sum_univ_of (prodEquivTensor R M N n x), map_sum]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    by_cases hk : (k : ℕ) < i
    · rw [hx k hk, map_zero, map_zero]
      exact zero_mem _
    · rw [← DirectSum.lof_eq_of R, prodEquivTensor_symm_lof]
      exact exteriorPowerFiltration_antitone _ _ (not_lt.mp hk)
        (wedgeTensor_mem_exteriorPowerFiltration _ _ _ _ _)

/-- The inverse of the exterior sum comparison carries the summand `⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N` into the `i`th
step of the extension filtration of the first factor. -/
theorem prodEquivTensor_symm_lof_mem_exteriorPowerFiltration (n : ℕ) (i : Fin (n + 1))
    (t : ⋀[R]^(i : ℕ) M ⊗[R] ⋀[R]^(n - i) N) :
    (prodEquivTensor R M N n).symm (DirectSum.lof R _ _ i t) ∈
      (LinearMap.range (LinearMap.inl R M N)).exteriorPowerFiltration n i := by
  rw [prodEquivTensor_symm_lof]
  exact wedgeTensor_mem_exteriorPowerFiltration _ _ _ _ _

/-- The `i`th component of the exterior sum comparison, restricted to the `i`th step `Fⁱ` of the
extension filtration of the first factor of `M × N`. It is surjective
(`prodFiltrationComponent_surjective`) with kernel `Fⁱ⁺¹` (`ker_prodFiltrationComponent`). -/
def prodFiltrationComponent (n : ℕ) (i : Fin (n + 1)) :
    (LinearMap.range (LinearMap.inl R M N)).exteriorPowerFiltration n i →ₗ[R]
      ⋀[R]^(i : ℕ) M ⊗[R] ⋀[R]^(n - i) N :=
  DirectSum.component R _ _ i ∘ₗ (prodEquivTensor R M N n).toLinearMap ∘ₗ Submodule.subtype _

/-- `prodFiltrationComponent` is the `i`th component of the exterior sum comparison. -/
@[simp]
theorem prodFiltrationComponent_apply (n : ℕ) (i : Fin (n + 1))
    (x : (LinearMap.range (LinearMap.inl R M N)).exteriorPowerFiltration n i) :
    prodFiltrationComponent n i x = prodEquivTensor R M N n x i :=
  (rfl)

/-- `prodFiltrationComponent` sends the wedge product of `t ∈ ⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N` back to `t`. -/
theorem prodFiltrationComponent_prodEquivTensor_symm_lof (n : ℕ) (i : Fin (n + 1))
    (t : ⋀[R]^(i : ℕ) M ⊗[R] ⋀[R]^(n - i) N) :
    prodFiltrationComponent n i
      ⟨_, prodEquivTensor_symm_lof_mem_exteriorPowerFiltration n i t⟩ = t := by
  rw [prodFiltrationComponent_apply, LinearEquiv.apply_symm_apply, DirectSum.lof_eq_of,
    DirectSum.of_eq_same]

/-- `prodFiltrationComponent` maps `Fⁱ` onto `⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N`. -/
theorem prodFiltrationComponent_surjective (n : ℕ) (i : Fin (n + 1)) :
    Function.Surjective (prodFiltrationComponent (R := R) (M := M) (N := N) n i) := fun t ↦
  ⟨_, prodFiltrationComponent_prodEquivTensor_symm_lof n i t⟩

/-- The kernel of `prodFiltrationComponent` on `Fⁱ` is `Fⁱ⁺¹`. -/
theorem ker_prodFiltrationComponent (n : ℕ) (i : Fin (n + 1)) :
    LinearMap.ker (prodFiltrationComponent (R := R) (M := M) (N := N) n i) =
      ((LinearMap.range (LinearMap.inl R M N)).exteriorPowerFiltration n ((i : ℕ) + 1)).comap
        ((LinearMap.range (LinearMap.inl R M N)).exteriorPowerFiltration n i).subtype := by
  ext x
  have hx := mem_exteriorPowerFiltration_range_inl_iff.mp x.property
  rw [LinearMap.mem_ker, prodFiltrationComponent_apply, Submodule.mem_comap,
    Submodule.subtype_apply, mem_exteriorPowerFiltration_range_inl_iff]
  refine ⟨fun h k hk ↦ ?_, fun h ↦ h i (Nat.lt_succ_self _)⟩
  rcases (Nat.lt_succ_iff.mp hk).lt_or_eq with hk | hk
  · exact hx k hk
  · rwa [Fin.ext hk]

end exteriorPower

end TauCeti
