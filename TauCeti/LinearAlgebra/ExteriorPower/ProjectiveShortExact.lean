/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.FreeShortExact
public import TauCeti.LinearAlgebra.ExteriorPower.Invertible
public import TauCeti.LinearAlgebra.ExteriorPower.Prod

/-!
# Determinants of exact sequences of finite projective modules

Let `0 → M → N → P → 0` be a short exact sequence of modules over a commutative ring `R`, with
maps `f : M → N` and `q : N → P`, where `M` and `P` are finite projective of constant ranks `n`
and `r`. The determinant of a finite projective module of constant rank is its top exterior power,
and this file constructs the canonical isomorphism

`⋀ⁿ M ⊗ ⋀ʳ P ≃ ⋀ⁿ⁺ʳ N`, `(m₁ ∧ ⋯ ∧ mₙ) ⊗ (p₁ ∧ ⋯ ∧ pᵣ) ↦ f m₁ ∧ ⋯ ∧ f mₙ ∧ z₁ ∧ ⋯ ∧ zᵣ`,

where `zⱼ` is any lift of `pⱼ` along `q` (`TauCeti.exteriorPower.shortExactEquivOfProjective`).
This is the exact-sequence additivity `det N ≃ det M ⊗ det P` of the determinant, with the factor
of the submodule first. It extends `TauCeti.exteriorPower.shortExactEquivOfBasis`, the comparison
for modules with finite bases, to modules that need not be free, and agrees with it whenever both
are defined.

The value on wedges does not depend on the lifts. In fact, as soon as `⋀ⁿ⁺¹ M = 0`, the wedge
`f m₁ ∧ ⋯ ∧ f mₙ ∧ z₁ ∧ ⋯ ∧ zᵣ` is unchanged when the `zⱼ` move by vectors in the image of `f`
(`TauCeti.exteriorPower.ιMulti_append_eq_of_sub_mem_range`): moving any one of them adds a wedge
with `n + 1` factors from the image of `f`. Such a wedge is the image of an element of
`⋀ⁿ⁺¹ M = 0`.

To construct the isomorphism, the sequence is split, `N ≃ M × P`, which is possible since `P` is
projective. The wedge product `⋀ⁿ M ⊗ ⋀ʳ P → ⋀ⁿ⁺ʳ (M × P)` is surjective, because every other
bidegree `(i, n + r - i)` of `⋀ⁿ⁺ʳ (M × P)` has a vanishing factor `⋀ⁱ M` (if `i > n`) or
`⋀ⁿ⁺ʳ⁻ⁱ P` (if `i < n`). Both sides are invertible modules, so the surjection is an isomorphism.
The wedge formula then shows that the result does not depend on the splitting, and characterizes
the isomorphism (`TauCeti.exteriorPower.shortExactEquivOfProjective_unique`).

## Main declarations

* `TauCeti.exteriorPower.ιMulti_append_eq_of_sub_mem_range`: wedges with `n` factors from the
  image of `f` followed by other factors depend on the other factors only modulo the image of `f`,
  when `⋀ⁿ⁺¹ M = 0`.
* `TauCeti.exteriorPower.wedgeTensor_bijective`: for `M` and `P` finite projective of constant
  ranks `n` and `r`, the wedge product `⋀ⁿ M ⊗ ⋀ʳ P → ⋀ⁿ⁺ʳ (M × P)` is bijective.
* `TauCeti.exteriorPower.shortExactEquivOfProjective`: the isomorphism `⋀ⁿ M ⊗ ⋀ʳ P ≃ ⋀ⁿ⁺ʳ N`.
* `TauCeti.exteriorPower.shortExactEquivOfProjective_tmul_ιMulti`: its value on wedges, for
  arbitrary lifts, and `TauCeti.exteriorPower.shortExactEquivOfProjective_unique`: this value
  determines it.
* `TauCeti.exteriorPower.shortExactEquivOfProjective_eq_shortExactEquivOfBasis`: for modules with
  finite bases, it is the comparison of `TauCeti.exteriorPower.shortExactEquivOfBasis`.
* `TauCeti.exteriorPower.map_comp_shortExactEquivOfProjective`: naturality with respect to maps of
  short exact sequences.
* `TauCeti.exteriorPower.shortExactEquivOfProjective_baseChange`: compatibility with base change
  along any commutative `R`-algebra.
* `TauCeti.exteriorPower.shortExactEquivOfProjective_inl_snd`: for the split sequence
  `M → M × P → P`, it is the wedge product `TauCeti.exteriorPower.wedgeTensor`, the ordered sum
  comparison.

## References

* C. A. Weibel, *The K-book*, Chapter I, §3 (determinants of finite projective modules, and
  `det N ≃ det M ⊗ det P` for a short exact sequence).
-/

public section

noncomputable section

open Module TensorProduct

namespace TauCeti.exteriorPower

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

section Lifts

variable {n r : ℕ} [Subsingleton (⋀[R]^(n + 1) M)] (f : M →ₗ[R] N) (v : Fin n → M)

/-- If `⋀ⁿ⁺¹ M = 0`, then `f v₁ ∧ ⋯ ∧ f vₙ ∧ f u = 0`, as the image of `v₁ ∧ ⋯ ∧ vₙ ∧ u`. -/
private theorem ιMulti_comp_mul_ι_eq_zero (u : M) :
    ExteriorAlgebra.ιMulti R n (f ∘ v) * ExteriorAlgebra.ι R (f u) = 0 := by
  have hmem : ExteriorAlgebra.ιMulti R n v * ExteriorAlgebra.ι R u ∈ ⋀[R]^(n + 1) M :=
    SetLike.mul_mem_graded (_root_.exteriorPower.ιMulti R n v).property
      (ExteriorAlgebra.ι_mem_exteriorPower_one u)
  have h0 : ExteriorAlgebra.ιMulti R n v * ExteriorAlgebra.ι R u = 0 :=
    congrArg Subtype.val (Subsingleton.elim (⟨_, hmem⟩ : ⋀[R]^(n + 1) M) 0)
  rw [← ExteriorAlgebra.map_apply_ιMulti, ← ExteriorAlgebra.map_apply_ι, ← map_mul, h0, map_zero]

/-- If `⋀ⁿ⁺¹ M = 0`, a wedge `f v₁ ∧ ⋯ ∧ f vₙ ∧ z₁ ∧ ⋯ ∧ zᵣ` in which some `zⱼ` lies in the
image of `f` vanishes. -/
private theorem ιMulti_comp_mul_ιMulti_eq_zero {z : Fin r → N} {j : Fin r}
    (hj : z j ∈ LinearMap.range f) :
    ExteriorAlgebra.ιMulti R n (f ∘ v) * ExteriorAlgebra.ιMulti R r z = 0 := by
  obtain ⟨u, hu⟩ := hj
  cases r with
  | zero => exact j.elim0
  | succ r =>
    let g := (LinearMap.mulLeft R (ExteriorAlgebra.ιMulti R n (f ∘ v))).compAlternatingMap
      (ExteriorAlgebra.ιMulti R (r + 1))
    -- The claim when the factor from the image of `f` comes first.
    have h0 (y : Fin (r + 1) → N) (hy : y 0 = f u) : g y = 0 := by
      simp [g, ExteriorAlgebra.ιMulti_succ_apply, hy, ← mul_assoc,
        ιMulti_comp_mul_ι_eq_zero f v u]
    by_cases hj0 : j = 0
    · subst hj0
      exact h0 z hu.symm
    · -- Otherwise move the factor `z j` to the front, at the cost of a sign.
      have h := g.map_swap z (Ne.symm hj0)
      rw [h0 _ (by simp [hu])] at h
      simpa [g] using neg_eq_zero.mp h.symm

/-- If `⋀ⁿ⁺¹ M = 0`, the wedge `f v₁ ∧ ⋯ ∧ f vₙ ∧ z₁ ∧ ⋯ ∧ zᵣ` depends on the `zⱼ` only modulo the
image of `f`. -/
theorem ιMulti_append_eq_of_sub_mem_range {z z' : Fin r → N}
    (h : ∀ j, z' j - z j ∈ LinearMap.range f) :
    _root_.exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z') =
      _root_.exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z) := by
  classical
  refine Subtype.ext ?_
  simp only [_root_.exteriorPower.ιMulti_apply_coe, ← ExteriorAlgebra.ιMulti_mul_ιMulti]
  let g := (LinearMap.mulLeft R (ExteriorAlgebra.ιMulti R n (f ∘ v))).compAlternatingMap
    (ExteriorAlgebra.ιMulti R r)
  -- Expand `g (z + (z' - z))` multilinearly; only the term `g z` survives.
  have hexp := g.toMultilinearMap.map_add_univ z (z' - z)
  rw [add_sub_cancel, Finset.sum_eq_single Finset.univ] at hexp
  · simpa [g] using hexp
  · intro s _ hs
    obtain ⟨j, hj⟩ : ∃ j, j ∉ s := by
      by_contra! hall
      exact hs (Finset.eq_univ_iff_forall.mpr hall)
    exact ιMulti_comp_mul_ιMulti_eq_zero f v (j := j)
      (by simpa [Finset.piecewise_eq_of_notMem _ _ _ hj] using h j)
  · simp

end Lifts

section Projective

variable [Module.Finite R M] [Module.Projective R M] [Module.Finite R P] [Module.Projective R P]
  {n r : ℕ}

/-- If `M` and `P` are finite projective of constant ranks `n` and `r`, the wedge product
`⋀ⁿ M ⊗ ⋀ʳ P → ⋀ⁿ⁺ʳ (M × P)` is surjective: the other bidegrees have a vanishing factor. -/
private theorem wedgeTensor_surjective (hM : ∀ p, rankAtStalk (R := R) M p = n)
    (hP : ∀ p, rankAtStalk (R := R) P p = r) :
    Function.Surjective (wedgeTensor R M P n r (n + r) rfl) := by
  intro x
  obtain ⟨y, hy⟩ : ∃ y : ExteriorAlgebra R M ⊗[R] ExteriorAlgebra R P,
      (ExteriorAlgebra.prodEquivTensor R M P).symm (GradedTensorProduct.of R _ _ y) = x :=
    ⟨(GradedTensorProduct.of R _ _).symm (ExteriorAlgebra.prodEquivTensor R M P x), by simp⟩
  have hsum := sum_coe_wedgeTensor_map_proj (n + r) y
  rw [hy, proj_coe, Finset.sum_eq_single ⟨n, by omega⟩] at hsum
  · -- The bidegree-`(n, r)` term, with `r` written as `n + r - n`.
    have key (p q : ℕ) (h : p + q = n + r) (t : ⋀[R]^p M ⊗[R] ⋀[R]^q P) (hp : p = n) :
        ∃ t', wedgeTensor R M P n r (n + r) rfl t' = wedgeTensor R M P p q (n + r) h t := by
      subst hp
      obtain rfl : q = r := by omega
      exact ⟨t, rfl⟩
    obtain ⟨t', ht'⟩ := key _ _ _ _ rfl
    exact ⟨t', ht'.trans (Subtype.ext hsum)⟩
  · intro i _ hi
    have hin : (i : ℕ) ≠ n := fun h ↦ hi (Fin.ext h)
    rcases lt_or_gt_of_ne hin with h | h
    · have : Subsingleton (⋀[R]^(n + r - i) P) :=
        exteriorPower.subsingleton_of_rankAtStalk_lt fun p ↦ by rw [hP]; omega
      simp [Subsingleton.elim (TensorProduct.map (proj R M i) (proj R P (n + r - i)) y) 0]
    · have : Subsingleton (⋀[R]^(i : ℕ) M) :=
        exteriorPower.subsingleton_of_rankAtStalk_lt fun p ↦ by rw [hM]; omega
      simp [Subsingleton.elim (TensorProduct.map (proj R M i) (proj R P (n + r - i)) y) 0]
  · simp

/-- If `M` and `P` are finite projective of constant ranks `n` and `r`, the wedge product
`⋀ⁿ M ⊗ ⋀ʳ P → ⋀ⁿ⁺ʳ (M × P)`, `a ⊗ b ↦ a ∧ b`, is bijective. -/
theorem wedgeTensor_bijective (hM : ∀ p, rankAtStalk (R := R) M p = n)
    (hP : ∀ p, rankAtStalk (R := R) P p = r) :
    Function.Bijective (wedgeTensor R M P n r (n + r) rfl) := by
  have := exteriorPower.invertible_of_rankAtStalk_eq hM
  have := exteriorPower.invertible_of_rankAtStalk_eq hP
  have : Module.Invertible R (⋀[R]^(n + r) (M × P)) :=
    exteriorPower.invertible_of_rankAtStalk_eq fun p ↦ by
      rw [rankAtStalk_prod, Pi.add_apply, hM, hP]
  exact Module.Invertible.bijective_of_surjective (wedgeTensor_surjective hM hP)

variable {f : M →ₗ[R] N} {q : N →ₗ[R] P} (hf : Function.Injective f) (he : Function.Exact f q)
  (hq : Function.Surjective q) (hM : ∀ p, rankAtStalk (R := R) M p = n)
  (hP : ∀ p, rankAtStalk (R := R) P p = r)

/-- A splitting `N ≃ M × P` of a short exact sequence with projective quotient `P`. -/
private def splitting :
    {e : N ≃ₗ[R] M × P // f = e.symm ∘ₗ LinearMap.inl R M P ∧ q = LinearMap.snd R M P ∘ₗ e} :=
  he.splitSurjectiveEquiv hf
    ⟨_, (q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)).choose_spec⟩

/-- For a short exact sequence `0 → M → N → P → 0` of modules over a commutative ring, with `M`
and `P` finite projective of constant ranks `n` and `r`, the canonical isomorphism
`⋀ⁿ M ⊗ ⋀ʳ P ≃ ⋀ⁿ⁺ʳ N`. It sends `(m₁ ∧ ⋯ ∧ mₙ) ⊗ (p₁ ∧ ⋯ ∧ pᵣ)` to
`f m₁ ∧ ⋯ ∧ f mₙ ∧ z₁ ∧ ⋯ ∧ zᵣ` for any lifts `zⱼ` of the `pⱼ`
(`TauCeti.exteriorPower.shortExactEquivOfProjective_tmul_ιMulti`), which determines it. -/
def shortExactEquivOfProjective : ⋀[R]^n M ⊗[R] ⋀[R]^r P ≃ₗ[R] ⋀[R]^(n + r) N :=
  (LinearEquiv.ofBijective _ (wedgeTensor_bijective hM hP)).trans
    ((splitting hf he hq).val.symm.exteriorPower (n + r))

/-- The determinant comparison sends a wedge tensored with the wedge of quotient images to the
wedge of the submodule images followed by the arbitrary lifts. -/
@[simp]
theorem shortExactEquivOfProjective_tmul_ιMulti (v : Fin n → M) (z : Fin r → N) :
    shortExactEquivOfProjective hf he hq hM hP
        (_root_.exteriorPower.ιMulti R n v ⊗ₜ[R] _root_.exteriorPower.ιMulti R r (q ∘ z)) =
      _root_.exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z) := by
  have : Subsingleton (⋀[R]^(n + 1) M) :=
    exteriorPower.subsingleton_of_rankAtStalk_lt fun p ↦ by rw [hM]; omega
  simp only [shortExactEquivOfProjective, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    wedgeTensor_tmul_ιMulti, LinearEquiv.exteriorPower_apply_ιMulti]
  generalize splitting hf he hq = s
  obtain ⟨e, hfe, hqe⟩ := s
  -- The splitting lifts `q ∘ z` to `s ∘ q ∘ z`, with the section `s = e.symm ∘ inr`.
  have hcomp : e.symm ∘ (Fin.append (LinearMap.inl R M P ∘ v) (LinearMap.inr R M P ∘ (q ∘ z)) ∘
      Fin.cast rfl) = Fin.append (f ∘ v) (e.symm ∘ LinearMap.inr R M P ∘ q ∘ z) := by
    ext i
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i <;> simp [hfe]
  rw [hcomp]
  refine ιMulti_append_eq_of_sub_mem_range f v fun j ↦ (he _).1 ?_
  have hqs : q (e.symm (0, q (z j))) = q (z j) := by simp [hqe]
  simp [hqs]

/-- The inverse determinant comparison separates the submodule wedge from the quotient wedge. -/
@[simp]
theorem shortExactEquivOfProjective_symm_ιMulti (v : Fin n → M) (z : Fin r → N) :
    (shortExactEquivOfProjective hf he hq hM hP).symm
        (_root_.exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z)) =
      _root_.exteriorPower.ιMulti R n v ⊗ₜ[R] _root_.exteriorPower.ιMulti R r (q ∘ z) :=
  (LinearEquiv.symm_apply_eq _).2 (shortExactEquivOfProjective_tmul_ιMulti hf he hq hM hP v z).symm

/-- The wedge formula determines the determinant comparison among all linear maps. -/
theorem shortExactEquivOfProjective_unique
    (φ : ⋀[R]^n M ⊗[R] ⋀[R]^r P →ₗ[R] ⋀[R]^(n + r) N)
    (h : ∀ (v : Fin n → M) (z : Fin r → N),
      φ (_root_.exteriorPower.ιMulti R n v ⊗ₜ[R] _root_.exteriorPower.ιMulti R r (q ∘ z)) =
        _root_.exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z)) :
    φ = shortExactEquivOfProjective hf he hq hM hP := by
  refine TensorProduct.ext (_root_.exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦
    _root_.exteriorPower.linearMap_ext (AlternatingMap.ext fun w ↦ ?_)))
  obtain ⟨z, rfl⟩ := hq.comp_left w
  simp [h]

/-- For modules with finite bases, the determinant comparison is the one of
`TauCeti.exteriorPower.shortExactEquivOfBasis`. -/
theorem shortExactEquivOfProjective_eq_shortExactEquivOfBasis (b : Basis (Fin n) R M)
    (c : Basis (Fin r) R P) :
    shortExactEquivOfProjective hf he hq hM hP = shortExactEquivOfBasis hf he hq b c :=
  shortExactEquivOfBasis_unique hf he hq b c _
    (shortExactEquivOfProjective_tmul_ιMulti hf he hq hM hP)

/-- The determinant comparison is natural with respect to maps of short exact sequences: for maps
`α`, `β`, `γ` of the three terms commuting with the maps of the sequences,
`⋀ β (comparison (a ⊗ b)) = comparison (⋀ α a ⊗ ⋀ γ b)`. -/
theorem map_comp_shortExactEquivOfProjective {M' N' P' : Type*} [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N'] [AddCommGroup P'] [Module R P'] [Module.Finite R M']
    [Module.Projective R M'] [Module.Finite R P'] [Module.Projective R P']
    {f' : M' →ₗ[R] N'} {q' : N' →ₗ[R] P'} (hf' : Function.Injective f')
    (he' : Function.Exact f' q') (hq' : Function.Surjective q')
    (hM' : ∀ p, rankAtStalk (R := R) M' p = n) (hP' : ∀ p, rankAtStalk (R := R) P' p = r)
    (α : M →ₗ[R] M') (β : N →ₗ[R] N') (γ : P →ₗ[R] P') (hα : β ∘ₗ f = f' ∘ₗ α)
    (hγ : q' ∘ₗ β = γ ∘ₗ q) :
    _root_.exteriorPower.map (n + r) β ∘ₗ (shortExactEquivOfProjective hf he hq hM hP).toLinearMap =
      (shortExactEquivOfProjective hf' he' hq' hM' hP').toLinearMap ∘ₗ
        TensorProduct.map (_root_.exteriorPower.map n α) (_root_.exteriorPower.map r γ) := by
  refine TensorProduct.ext (_root_.exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦
    _root_.exteriorPower.linearMap_ext (AlternatingMap.ext fun w ↦ ?_)))
  obtain ⟨z, rfl⟩ := hq.comp_left w
  have hγz : γ ∘ (q ∘ z) = q' ∘ (β ∘ z) := funext fun j ↦ (LinearMap.congr_fun hγ (z j)).symm
  have hα' (x : M) : β (f x) = f' (α x) := LinearMap.congr_fun hα x
  have hβ : β ∘ Fin.append (f ∘ v) z = Fin.append (f' ∘ (α ∘ v)) (β ∘ z) := by
    ext i
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i <;> simp [hα']
  simp [hγz, hβ]

/-- The determinant comparison commutes with base change along any commutative `R`-algebra `A`:
under the identifications `⋀[A]ᵏ (A ⊗ X) ≃ A ⊗ ⋀[R]ᵏ X` of
`TauCeti.exteriorPower.equivBaseChange`, the comparison of the base-changed sequence
`0 → A ⊗ M → A ⊗ N → A ⊗ P → 0` is the base change of the comparison. -/
theorem shortExactEquivOfProjective_baseChange (A : Type*) [CommRing A] [Algebra R A]
    (hfA : Function.Injective (f.baseChange A))
    (heA : Function.Exact (f.baseChange A) (q.baseChange A))
    (hqA : Function.Surjective (q.baseChange A))
    (hMA : ∀ p, rankAtStalk (R := A) (A ⊗[R] M) p = n)
    (hPA : ∀ p, rankAtStalk (R := A) (A ⊗[R] P) p = r) (a : ⋀[R]^n M) (b : ⋀[R]^r P) :
    shortExactEquivOfProjective hfA heA hqA hMA hPA
        ((equivBaseChange A n).symm (1 ⊗ₜ a) ⊗ₜ[A] (equivBaseChange A r).symm (1 ⊗ₜ b)) =
      (equivBaseChange A (n + r)).symm
        (1 ⊗ₜ shortExactEquivOfProjective hf he hq hM hP (a ⊗ₜ b)) := by
  have ha : a ∈ Submodule.span R (Set.range (_root_.exteriorPower.ιMulti R n)) := by
    rw [_root_.exteriorPower.ιMulti_span]
    trivial
  have hb : b ∈ Submodule.span R (Set.range (_root_.exteriorPower.ιMulti R r)) := by
    rw [_root_.exteriorPower.ιMulti_span]
    trivial
  -- Both sides are additive and `R`-linear in `a` and `b`, so it suffices to check wedges.
  induction ha using Submodule.span_induction generalizing b with
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx b hb, hy b hb]
  | smul c x _ hx =>
    simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← algebraMap_smul A c,
      map_smul, hx b hb]
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | zero => simp
    | add y y' _ _ hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | smul c y _ hy =>
      simp only [TensorProduct.tmul_smul, ← algebraMap_smul A c, map_smul, hy]
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      obtain ⟨z, rfl⟩ := hq.comp_left w
      have hz : (fun j ↦ (1 : A) ⊗ₜ[R] (q ∘ z) j) = q.baseChange A ∘ fun j ↦ 1 ⊗ₜ z j :=
        funext fun j ↦ by simp
      have happ : Fin.append (f.baseChange A ∘ fun i ↦ (1 : A) ⊗ₜ[R] v i) (fun j ↦ 1 ⊗ₜ z j) =
          fun i ↦ 1 ⊗ₜ Fin.append (f ∘ v) z i := by
        ext i
        refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i <;> simp
      simp only [equivBaseChange_symm_tmul_ιMulti, one_smul, hz, happ,
        shortExactEquivOfProjective_tmul_ιMulti]

/-- For the split sequence `0 → M → M × P → P → 0`, the determinant comparison is the wedge product
`⋀ⁿ M ⊗ ⋀ʳ P → ⋀ⁿ⁺ʳ (M × P)` of the ordered sum, `a ⊗ b ↦ a ∧ b` with the factor of `M` first. -/
theorem shortExactEquivOfProjective_inl_snd (x : ⋀[R]^n M ⊗[R] ⋀[R]^r P) :
    shortExactEquivOfProjective LinearMap.inl_injective Function.Exact.inl_snd
        LinearMap.snd_surjective hM hP x = wedgeTensor R M P n r (n + r) rfl x := by
  have : Subsingleton (⋀[R]^(n + 1) M) :=
    exteriorPower.subsingleton_of_rankAtStalk_lt fun p ↦ by rw [hM]; omega
  refine (LinearMap.congr_fun (shortExactEquivOfProjective_unique _ _ _ hM hP
    (wedgeTensor R M P n r (n + r) rfl) fun v z ↦ ?_) x).symm
  rw [wedgeTensor_tmul_ιMulti, Fin.cast_refl, Function.comp_id]
  exact ιMulti_append_eq_of_sub_mem_range (LinearMap.inl R M P) v fun j ↦
    ⟨-(z j).1, by ext <;> simp⟩

end Projective

end TauCeti.exteriorPower
