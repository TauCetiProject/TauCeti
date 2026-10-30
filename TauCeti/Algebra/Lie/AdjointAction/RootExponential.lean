/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.Killing
public import TauCeti.Algebra.Lie.AdjointAction.InnerAutomorphismGroup
public import TauCeti.RingTheory.MvPolynomial.Dominant
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Module.Submodule.Union
import TauCeti.Algebra.DualNumber.Matrix
import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Root exponentials and the density of the conjugates of a Cartan subalgebra

Let `L` be a finite-dimensional Lie algebra over a field `K` of characteristic zero whose Killing
form is nondegenerate, and let `H` be a splitting Cartan subalgebra. Choose a nonzero vector
`e_α` in each root space and list the roots in some order `α₁, …, α_m`. The **root-exponential
map**

`φ(t, h) = exp(t₁ ad e_{α₁}) ⋯ exp(t_m ad e_{α_m}) h`,  `t ∈ K^m`, `h ∈ H`,

takes values in the conjugates `Int(L) · H` of `H` under the group `Int(L)` of inner automorphisms
(`TauCeti.intLieAlgebra`). Each `ad e_α` is nilpotent, so each exponential is a finite sum and the
coordinates of `φ` in a basis of `L` are polynomials in `t` and in the coordinates of `h`.

At a point `(0, h₀)` the differential of `φ` sends `(τ, η)` to `η + ∑ τ_α ⁅e_α, h₀⁆`, and
`⁅e_α, h₀⁆ = -α(h₀) e_α`. If no root vanishes at `h₀` (such an `h₀` exists because `K` is
infinite) the image of the differential contains `H` and every root space, so by the root space
decomposition it is all of `L`. A polynomial map whose differential is surjective at one point is
dominant (`TauCeti.eq_zero_of_forall_eval_eq_zero_of_mulVec_surjective_jacobiMatrixAt`), so:

**a polynomial function on `L` that vanishes on `Int(L) · H` is zero.**

This is the density statement on which the injectivity half of Chevalley's restriction theorem
rests: an `Int(L)`-invariant polynomial function vanishing on `H` vanishes on `Int(L) · H`, hence
everywhere.

The differential is computed by evaluating the coordinate polynomials at a dual-number point
(`TauCeti.jacobiMatrixAt_mulVec_apply_eq_snd_aeval`): every exponential becomes `1 + ε τ_α ad e_α`,
and the product of these is `1 + ε ∑ τ_α ad e_α` because `ε² = 0`.

## Main results

* `LieSubalgebra.exists_rootExponentialPolynomialParametrization`: a polynomial family, in the
  coordinates of a basis of `L`, whose values all lie in `Int(L) · H` and whose Jacobian matrix
  is surjective at some point.
* `LieSubalgebra.polynomial_eq_zero_of_intCartan`: a polynomial in the coordinates of a basis
  of `L` that vanishes on `Int(L) · H` is zero.
* `LieSubalgebra.polynomial_eq_zero_of_invariant_of_cartan`: an `Int(L)`-invariant polynomial
  that vanishes on `H` is zero.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1, where
  the injectivity of the Chevalley restriction map is proved by the density of `Int(L) · H`.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule MvPolynomial Matrix TrivSqZeroExt
  LinearMap.GeneralLinearGroup

/-! ### Truncated exponential series of matrices with coefficients in an algebra -/

section ExpSeries

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The exponential series of `x • A`, truncated below degree `d`, for a matrix `A` over `K` and a
scalar `x` in a commutative `K`-algebra `S`. It is a truncated sum rather than `IsNilpotent.exp`
so that it is defined over every commutative `K`-algebra, polynomial rings and dual numbers
included, and commutes with every `K`-algebra map. -/
private noncomputable def expSeries {S : Type*} [CommRing S] [Algebra K S] (A : Matrix ι ι K)
    (d : ℕ) (x : S) : Matrix ι ι S :=
  ∑ k ∈ Finset.range d, (x ^ k * algebraMap K S (k.factorial : K)⁻¹) • A.map (algebraMap K S) ^ k

/-- The truncated exponential series is natural in the coefficient algebra. -/
private theorem map_expSeries {S S' : Type*} [CommRing S] [Algebra K S] [CommRing S']
    [Algebra K S'] (f : S →ₐ[K] S') (A : Matrix ι ι K) (d : ℕ) (x : S) :
    f.mapMatrix (expSeries A d x) = expSeries A d (f x) := by
  have hsmul (r : S) (M : Matrix ι ι S) : f.mapMatrix (r • M) = f r • f.mapMatrix M := by
    ext i j
    simp
  simp only [expSeries, map_sum, hsmul, map_pow, map_mul, AlgHom.commutes]
  congr! 3
  ext i j
  simp

/-- With a square-zero coefficient `ε c`, the truncated exponential series is `1 + ε c A`. -/
private theorem expSeries_inr {d : ℕ} (hd : 2 ≤ d) (A : Matrix ι ι K) (c : K) :
    expSeries A d (inr c : TrivSqZeroExt K K) = 1 + (c • A).map inr := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hd
  have hsq (k : ℕ) : (inr c : TrivSqZeroExt K K) ^ (k + 1 + 1) = 0 := by
    rw [pow_succ, pow_succ, mul_assoc, inr_mul_inr, mul_zero]
  rw [expSeries, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero, zero_add]
  · simp only [zero_add, pow_one, pow_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      inv_one, map_one, mul_one, one_smul, add_comm (1 : Matrix ι ι _)]
    congr 1
    ext i j : 1
    simp [algebraMap_eq_inl, inr_mul_inl]
  · intro k _
    rw [hsq, zero_mul]
    ext i j : 1
    simp

end ExpSeries

/-! ### Products of truncated exponentials applied to a parametrized vector -/

section ExpProd

variable {K ι α κ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The vector `(∏_{a ∈ l} exp(t_a A_a)) (∑_j s_j c_j)`, with the exponentials truncated below
the degrees `d a`, for coefficients `t` and `s` in a commutative `K`-algebra `S`. -/
private noncomputable def expProdVec {S : Type*} [CommRing S] [Algebra K S] (l : List α)
    (A : α → Matrix ι ι K) (d : α → ℕ) (c : κ → ι → K) (t : α → S) (s : κ → S) : ι → S :=
  (l.map fun a ↦ expSeries (A a) (d a) (t a)).prod *ᵥ ∑ j, s j • fun i ↦ algebraMap K S (c j i)

private theorem map_expProdVec {S S' : Type*} [CommRing S] [Algebra K S] [CommRing S']
    [Algebra K S'] (f : S →ₐ[K] S') (l : List α) (A : α → Matrix ι ι K) (d : α → ℕ)
    (c : κ → ι → K) (t : α → S) (s : κ → S) (i : ι) :
    f (expProdVec l A d c t s i) = expProdVec l A d c (f ∘ t) (f ∘ s) i := by
  rw [expProdVec, expProdVec, ← f.coe_toRingHom, RingHom.map_mulVec, f.coe_toRingHom,
    ← AlgHom.mapMatrix_apply, map_list_prod, List.map_map]
  congr 1
  · exact congrArg List.prod (List.map_congr_left fun a _ ↦ map_expSeries f _ _ _)
  · ext i
    simp [map_sum]

/-- The polynomial coordinates of `(t, s) ↦ (∏_{a ∈ l} exp(t_a A_a)) (∑_j s_j c_j)`. -/
private noncomputable def expProdPoly (l : List α) (A : α → Matrix ι ι K) (d : α → ℕ)
    (c : κ → ι → K) (i : ι) : MvPolynomial (α ⊕ κ) K :=
  expProdVec l A d c (fun a ↦ X (Sum.inl a)) (fun j ↦ X (Sum.inr j)) i

private theorem eval_expProdPoly (l : List α) (A : α → Matrix ι ι K) (d : α → ℕ)
    (c : κ → ι → K) (x : α ⊕ κ → K) (i : ι) :
    eval x (expProdPoly l A d c i) =
      ((l.map fun a ↦ expSeries (A a) (d a) (x (Sum.inl a))).prod *ᵥ
        ∑ j, x (Sum.inr j) • c j) i := by
  have h := map_expProdVec (aeval x : MvPolynomial (α ⊕ κ) K →ₐ[K] K) l A d c
    (fun a ↦ X (Sum.inl a)) (fun j ↦ X (Sum.inr j)) i
  rw [aeval_eq_eval] at h
  rw [expProdPoly, h, expProdVec]
  simp

/-- **The differential of the parametrization at `t = 0`.** If every `d a` is at least `2`, the
Jacobian matrix at a point with vanishing `t`-coordinates sends a tangent vector `w` to
`(∑_{a ∈ l} w_a A_a) (∑_j s_j c_j) + ∑_j w_j c_j`. -/
private theorem jacobiMatrixAt_expProdPoly_mulVec [Fintype α] (l : List α)
    (A : α → Matrix ι ι K) {d : α → ℕ} (hd : ∀ a, 2 ≤ d a) (c : κ → ι → K) (s : κ → K)
    (w : α ⊕ κ → K) :
    jacobiMatrixAt (expProdPoly l A d c) (Sum.elim 0 s) *ᵥ w =
      (l.map fun a ↦ w (Sum.inl a) • A a).sum *ᵥ (∑ j, s j • c j) + ∑ j, w (Sum.inr j) • c j := by
  ext i
  rw [jacobiMatrixAt_mulVec_apply_eq_snd_aeval, expProdPoly, map_expProdVec, expProdVec]
  have hexp : ∀ a, expSeries (A a) (d a)
      ((aeval fun j ↦ inl (Sum.elim 0 s j) + inr (w j) : MvPolynomial (α ⊕ κ) K →ₐ[K] _)
        (X (Sum.inl a))) = 1 + (w (Sum.inl a) • A a).map inr := by
    intro a
    rw [aeval_X, Sum.elim_inl, Pi.zero_apply, inl_zero, zero_add, expSeries_inr (hd a)]
  have hvec : (∑ j, ((aeval fun j ↦ inl (Sum.elim 0 s j) + inr (w j) :
      MvPolynomial (α ⊕ κ) K →ₐ[K] _) (X (Sum.inr j))) •
        fun i ↦ algebraMap K (TrivSqZeroExt K K) (c j i)) =
      fun i ↦ inl ((∑ j, s j • c j) i) + inr ((∑ j, w (Sum.inr j) • c j) i) := by
    ext i
    · simp [algebraMap_eq_inl, Finset.sum_apply, fst_sum]
    · simp [algebraMap_eq_inl, Finset.sum_apply, snd_sum]
  simp only [Function.comp_def, hexp, hvec]
  rw [List.prod_map_one_add_map_inr, Matrix.one_add_map_inr_mulVec, snd_add, snd_inl, zero_add,
    snd_inr]

end ExpProd

/-! ### The root-exponential parametrization -/

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

section Exponential

variable [CharZero K] [LieAlgebra ℚ L]

/-- The truncated exponential series of the matrix of `ad e` is the matrix of `exp (ad (t • e))`,
once the truncation degree kills `ad e`. -/
private theorem toMatrixAlgEquiv_expAd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) {e : L} {d : ℕ} (hd : ad K L e ^ d = 0) (t : K)
    (ht : IsNilpotent (ad K L (t • e))) :
    LinearMap.toMatrixAlgEquiv b (expAd (t • e) ht).toLinearEquiv.toLinearMap =
      expSeries (LinearMap.toMatrixAlgEquiv b (ad K L e)) d t := by
  have hlin : (expAd (t • e) ht).toLinearEquiv.toLinearMap =
      ∑ k ∈ Finset.range d, ((k.factorial : K)⁻¹) • (t • ad K L e) ^ k := by
    ext y
    have hy : (ad K L (t • e) ^ d) y = 0 := by
      rw [map_smul, smul_pow, hd, smul_zero, LinearMap.zero_apply]
    simp only [LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv, LinearMap.sum_apply,
      expAd_apply_eq_sum ht hy]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hq := ratCast_smul_eq ℚ K ((k.factorial : ℚ)⁻¹) (((t • ad K L e) ^ k) y)
    rw [Rat.cast_id] at hq
    rw [map_smul, hq, LinearMap.smul_apply, Rat.cast_inv, Rat.cast_natCast]
  rw [hlin, expSeries, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, map_pow, map_smul, smul_pow, smul_smul, mul_comm]
  simp [Algebra.algebraMap_self]

end Exponential

variable (H : LieSubalgebra K L)

variable [CharZero K] [LieAlgebra ℚ L] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- **The root-exponential parametrization of the conjugates of a Cartan subalgebra.** Given a
basis `b` of `L` and a basis `bH` of the splitting Cartan subalgebra `H`, there is a family of
polynomials in one variable for each root and one for each basis vector of `H`, with these two
properties: its values, read in the coordinates of `b`, are all of the form `g h` with `g` in
`Int(L)` and `h ∈ H`, and its Jacobian matrix is surjective at some point. The polynomials are the
coordinates of `(t, h) ↦ ∏_α exp(t_α ad e_α) h` for chosen root vectors `e_α`. -/
theorem _root_.LieSubalgebra.exists_rootExponentialPolynomialParametrization {ι κ : Type*}
    [Finite ι] [Fintype κ] (b : Module.Basis ι K L) (bH : Module.Basis κ K H) :
    ∃ p : ι → MvPolynomial (H.root ⊕ κ) K,
      (∃ v, (jacobiMatrixAt p v).mulVec.Surjective) ∧
      ∀ x, ∃ g ∈ intLieAlgebra K L, ∃ h ∈ H, b.equivFun (g • h) = fun i ↦ eval x (p i) := by
  classical
  have := Fintype.ofFinite ι
  have hα0 (α : H.root) : α.1.IsNonZero := (Finset.mem_filter.mp α.2).2
  -- A nonzero root vector in each root space, and a nilpotency degree of its adjoint action.
  have hroot (α : H.root) : ∃ e ∈ rootSpace H α.1, e ≠ 0 :=
    α.1.exists_ne_zero
  choose e he he0 using hroot
  have hnil (α : H.root) : IsNilpotent (ad K L (e α)) :=
    isNilpotent_ad_of_mem_rootSpace H (fun h ↦ hα0 α ((Weight.coe_eq_zero_iff _).mp h)) (he α)
  choose n hn using hnil
  set d : H.root → ℕ := fun α ↦ n α + 2
  have hd (α) : ad K L (e α) ^ d α = 0 := by rw [pow_add, hn, zero_mul]
  have hnil' (α) (t : K) : IsNilpotent (ad K L (t • e α)) :=
    ⟨d α, by rw [map_smul, smul_pow, hd, smul_zero]⟩
  set l := (Finset.univ : Finset H.root).toList
  set A := fun α ↦ LinearMap.toMatrixAlgEquiv b (ad K L (e α))
  set c := fun j ↦ b.equivFun (bH j : L)
  refine ⟨expProdPoly l A d c, ?_, fun x ↦ ?_⟩
  · -- A point `h₀` of `H` at which no root vanishes.
    obtain ⟨h₀, hh₀⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
      (fun α : H.root ↦ Weight.toLinear K H L α.1) fun α ↦ by
        by_contra! h
        exact hα0 α ((Weight.coe_eq_zero_iff _).mp (funext fun x ↦ by simpa using h x))
    set s := bH.equivFun h₀
    have hs : ∑ j, s j • c j = b.equivFun (h₀ : L) := by
      conv_rhs => rw [← bH.sum_repr h₀]
      rw [AddSubmonoidClass.coe_finsetSum, map_sum]
      simp [s, c]
    refine ⟨Sum.elim 0 s, fun y ↦ ?_⟩
    -- The differential is `b.equivFun ∘ Λ` for the linear combination `Λ` of the vectors `v`.
    set v : H.root ⊕ κ → L :=
      Sum.elim (fun α ↦ ⁅e α, (h₀ : L)⁆) fun j ↦ (bH j : L)
    have hJ (w) : jacobiMatrixAt (expProdPoly l A d c) (Sum.elim 0 s) *ᵥ w =
        b.equivFun (Fintype.linearCombination K v w) := by
      rw [jacobiMatrixAt_expProdPoly_mulVec l A (fun _ ↦ le_add_self) c s w,
        Fintype.linearCombination_apply, Fintype.sum_sum_type, map_add, hs]
      congr 1
      · have hA : (l.map fun α ↦ w (Sum.inl α) • A α).sum =
            LinearMap.toMatrixAlgEquiv b (∑ α, w (Sum.inl α) • ad K L (e α)) := by
          simp [l, A, Finset.sum_map_toList, map_sum]
        rw [hA]
        refine (LinearMap.toMatrix_mulVec_repr b b _ _).trans ?_
        simp [v, map_sum]
      · simp [v, c, map_sum]
    -- The linear combinations of the `v`s are all of `L`, by the root space decomposition.
    have hspan : Submodule.span K (Set.range v) = ⊤ := by
      rw [eq_top_iff, ← LieSubmodule.top_toSubmodule (R := K) (L := H) (M := L),
        ← iSup_genWeightSpace_eq_top' K H L,
        LieSubmodule.iSup_toSubmodule, iSup_le_iff]
      intro χ z hz
      rw [LieSubmodule.mem_toSubmodule] at hz
      by_cases hχ : χ.IsZero
      · -- `rootSpace H χ` is by definition the weight space `genWeightSpace L χ`.
        have hzH : z ∈ rootSpace H 0 := by rwa [← (Weight.coe_eq_zero_iff χ).mpr hχ]
        rw [rootSpace_zero_eq K L H, LieSubalgebra.mem_toLieSubmodule] at hzH
        lift z to H using hzH
        rw [← bH.sum_repr z, AddSubmonoidClass.coe_finsetSum]
        exact Submodule.sum_mem _ fun j _ ↦
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
      · set α : H.root := ⟨χ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hχ⟩⟩
        obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e α, he α⟩ : rootSpace H χ)
          (by simpa [Subtype.ext_iff] using he0 α)).mp (finrank_rootSpace_eq_one χ hχ) ⟨z, hz⟩
        have hz' : z = r • e α := by simpa [Subtype.ext_iff] using hr.symm
        have hbr : ⁅e α, (h₀ : L)⁆ = -(χ h₀) • e α := by
          rw [← lie_skew, ← LieSubalgebra.coe_bracket_of_module,
            lie_eq_smul_of_mem_rootSpace (he α) h₀, neg_smul]
        have hχh₀ : χ h₀ ≠ 0 := by simpa using hh₀ α
        have he' : e α = (-(χ h₀))⁻¹ • ⁅e α, (h₀ : L)⁆ := by
          rw [hbr, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hχh₀), one_smul]
        rw [hz', he']
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
          (Submodule.subset_span ⟨Sum.inl α, rfl⟩))
    obtain ⟨w, hw⟩ : b.equivFun.symm y ∈ LinearMap.range (Fintype.linearCombination K v) := by
      rw [Fintype.range_linearCombination, hspan]
      trivial
    exact ⟨w, by rw [hJ, hw, LinearEquiv.apply_symm_apply]⟩
  · -- The value at `x` is `g h` for a product `g` of root exponentials and `h ∈ H`.
    refine ⟨(l.map fun α ↦ ofLinearEquiv (expAd (x (Sum.inl α) • e α)
        (hnil' α _)).toLinearEquiv).prod, list_prod_mem fun g hg ↦ ?_,
      ∑ j, x (Sum.inr j) • (bH j : L), H.sum_mem fun j _ ↦ H.smul_mem _ (bH j).2, ?_⟩
    · obtain ⟨α, -, rfl⟩ := List.mem_map.mp hg
      exact ofLinearEquiv_expAd_mem_intLieAlgebra _ _
    · ext i
      rw [eval_expProdPoly, b.equivFun_list_prod_smul]
      congr 2
      · refine List.map_congr_left fun α _ ↦ ?_
        exact toMatrixAlgEquiv_expAd b (hd α) _ _
      · simp [c, map_sum]

/-- **A polynomial vanishing on the conjugates of a Cartan subalgebra is zero.** In the coordinates
of a basis `b` of `L`, a polynomial that vanishes at `g h` for every inner automorphism
`g ∈ Int(L)` and every `h` in the splitting Cartan subalgebra `H` is the zero polynomial. -/
theorem _root_.LieSubalgebra.polynomial_eq_zero_of_intCartan {ι : Type*} [Finite ι]
    (b : Module.Basis ι K L) {q : MvPolynomial ι K}
    (hq : ∀ g ∈ intLieAlgebra K L, ∀ h ∈ H, eval (b.equivFun (g • h)) q = 0) : q = 0 := by
  obtain ⟨p, ⟨v, hv⟩, hp⟩ :=
    H.exists_rootExponentialPolynomialParametrization b (Module.finBasis K H)
  refine eq_zero_of_forall_eval_eq_zero_of_mulVec_surjective_jacobiMatrixAt hv fun x ↦ ?_
  obtain ⟨g, hg, h, hh, hgh⟩ := hp x
  rw [← hgh]
  exact hq g hg h hh

/-- **Chevalley injectivity on polynomials.** In the coordinates of a basis `b` of `L`, a
polynomial invariant under the inner automorphisms `Int(L)` that vanishes on the splitting Cartan
subalgebra `H` is the zero polynomial. -/
theorem _root_.LieSubalgebra.polynomial_eq_zero_of_invariant_of_cartan {ι : Type*} [Finite ι]
    (b : Module.Basis ι K L) {q : MvPolynomial ι K}
    (hinv : ∀ g ∈ intLieAlgebra K L, ∀ x : L, eval (b.equivFun (g • x)) q = eval (b.equivFun x) q)
    (hH : ∀ h ∈ H, eval (b.equivFun h) q = 0) : q = 0 :=
  H.polynomial_eq_zero_of_intCartan b fun g hg h hh ↦ (hinv g hg h).trans (hH h hh)

end TauCeti
