/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Matrix.Basic
public import TauCeti.RingTheory.HochschildCohomology.Complex
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Matrix Morita invariance of Hochschild cohomology

For an `R`-algebra `A`, an `R`-module `M`, and a finite nonempty index type `ι`, the generalized
matrix trace `φ ↦ φ#Tr` (`TauCeti.matrixCochainExtension`) induces an isomorphism on Hochschild
cohomology

`HHⁿ(A, Hom_R(A, M)) ≃ₗ[R] HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))`

when `A` is unital.

Fixing a matrix index `r : ι`, restricting a matrix cochain `ψ` to the `(r, r)` diagonal corner
`a ↦ Matrix.single r r a` defines a cochain map `TauCeti.matrixCornerRestriction` in the opposite
direction. By `TauCeti.matrixCochainExtension_single`, corner restriction is a strict left inverse
to `φ ↦ φ#Tr` on cochains, even for nonunital and nonassociative `A`.

When `A` has a two-sided identity `1`, the other composite `(corner_r ψ)#Tr` is cochain homotopic
to the identity on `C*(Matrix ι ι A; M)`. Explicitly, the prism homotopy
`TauCeti.matrixHochschildHomotopy` sends an `(n + 1)`-cochain `ψ` (a multilinear map in `n + 2`
matrix arguments) to the `n`-cochain `Hₙ ψ` given on `(X₀, …, Xₙ)` by

`(Hₙ ψ)(X₀, …, Xₙ) = ∑_{k = 0}^n (-1)ᵏ ∑_{q₀, …, q_{k+1} ∈ ι}`
`  ψ(E_{q₀, r}(X₀(q₀, q₁)), E_{r, r}(X₁(q₁, q₂)), …, E_{r, r}(Xₖ(qₖ, q_{k+1})),`
`    E_{r, q_{k+1}}(1), X_{k+1}, …, Xₙ)`.

In degree zero this satisfies `H₀ (b ψ) = ψ - (corner_r ψ)#Tr`, and in degree `m + 1` it satisfies
`b (Hₘ ψ) + Hₘ₊₁ (b ψ) = ψ - (corner_r ψ)#Tr`: the off-diagonal faces of `Hₘ₊₁ (b ψ)` cancel
`b (Hₘ ψ)`, the interior adjacent faces telescope in `k`, the initial face `(k, i) = (0, 0)`
reconstructs `X₀` from its matrix units to give `ψ`, and the final face `(k, i) = (m + 1, m + 2)`
closes the index path via `E_{r, q_{m+2}}(1) E_{q₀, r}(X₀(q₀, q₁))` to give `-(corner_r ψ)#Tr`.

## Main definitions

* `TauCeti.matrixCornerRestriction`: restriction of a matrix cochain to the `(r, r)` corner.
* `TauCeti.matrixHochschildHomotopy`: the prism cochain homotopy `Hₙ` between the identity on
  matrix cochains and `(corner_r ·)#Tr`.
* `TauCeti.hochschildCohomology.matrixExtension`: the map on Hochschild cohomology induced by
  `φ ↦ φ#Tr`.
* `TauCeti.hochschildCohomology.cornerRestriction`: the map on Hochschild cohomology induced by
  corner restriction.
* `TauCeti.hochschildCohomology.matrixExtensionEquiv`: the Morita linear equivalence on Hochschild
  cohomology for a unital algebra and nonempty finite index type.

## Main results

* `TauCeti.matrixCornerRestriction_matrixCochainExtension`: corner restriction is a left inverse to
  matrix cochain extension.
* `TauCeti.matrixCornerRestriction_hochschildCoboundary`: corner restriction commutes with the
  Hochschild coboundary.
* `TauCeti.matrixHochschildHomotopy_hochschildCoboundary_zero`,
  `TauCeti.hochschildCoboundary_matrixHochschildHomotopy_add`: the cochain homotopy identities
  `H₀ (b ψ) = ψ - (corner_r ψ)#Tr` and `b (Hₘ ψ) + Hₘ₊₁ (b ψ) = ψ - (corner_r ψ)#Tr`.
* `TauCeti.hochschildCohomology.bijective_matrixExtension`: matrix extension on Hochschild
  cohomology is bijective for a unital algebra and nonempty finite index type.

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II, §5.
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §1.2.
-/

public section

noncomputable section

namespace TauCeti

open scoped BigOperators

/-! ### Corner restriction of multilinear cochains -/

section CornerRestriction

variable {R A M ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid M] [Module R M] [SMulCommClass R R M] [DecidableEq ι]

/-- Restrict a degree-`n` cochain on `Matrix ι ι A` to the `(r, r)` diagonal corner by evaluating
every argument on `Matrix.single r r`. -/
def matrixCornerRestriction (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M where
  toFun ψ := ψ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r
  map_add' ψ χ := by
    ext x
    simp [MultilinearMap.compLinearMap_apply]
  map_smul' c ψ := by
    ext x
    simp [MultilinearMap.compLinearMap_apply]

/-- Evaluating the `(r, r)` corner restriction of `ψ` on `(x₀, …, xₙ)` evaluates `ψ` on the corner
matrices `(E_{r,r}(x₀), …, E_{r,r}(xₙ))`. -/
@[simp]
theorem matrixCornerRestriction_apply (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (x : Fin (n + 1) → A) :
    matrixCornerRestriction r n ψ x = ψ fun j ↦ Matrix.single r r (x j) :=
  (rfl)

/-- Corner restriction is a left inverse to matrix cochain extension. -/
@[simp]
theorem matrixCornerRestriction_matrixCochainExtension [Fintype ι] (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCornerRestriction r n (matrixCochainExtension ι n φ) = φ := by
  ext x
  exact matrixCochainExtension_single ι r n φ x

/-- Corner restriction composed with matrix cochain extension is the identity linear map. -/
@[simp]
theorem matrixCornerRestriction_comp_matrixCochainExtension [Fintype ι] (r : ι) (n : ℕ) :
    matrixCornerRestriction (R := R) (A := A) (M := M) r n ∘ₗ matrixCochainExtension ι n =
      LinearMap.id :=
  LinearMap.ext (matrixCornerRestriction_matrixCochainExtension r n)

end CornerRestriction

section CornerCoboundary

variable {R A M ι : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [DecidableEq ι] [Fintype ι]

/-- Corner restriction commutes with each Hochschild coface, since `a ↦ Matrix.single r r a` is
multiplicative. -/
theorem matrixCornerRestriction_hochschildCoface [AddCommMonoid M] [Module R M]
    [SMulCommClass R R M] (r : ι) (n : ℕ) (i : Fin (n + 2))
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCornerRestriction r (n + 1) (hochschildCoface R (Matrix ι ι A) M i ψ) =
      hochschildCoface R A M i (matrixCornerRestriction r n ψ) := by
  let e : A →ₙ* Matrix ι ι A :=
    ⟨Matrix.single r r, fun x y ↦ (Matrix.single_mul_single_same x r r r y).symm⟩
  ext x
  simp only [matrixCornerRestriction_apply, hochschildCoface_apply]
  exact congrArg ψ (comp_hochschildFace e i x).symm

/-- Corner restriction commutes with the Hochschild coboundary. -/
theorem matrixCornerRestriction_hochschildCoboundary [AddCommGroup M] [Module R M]
    [SMulCommClass R R M] (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCornerRestriction r (n + 1) (hochschildCoboundary R (Matrix ι ι A) M n ψ) =
      hochschildCoboundary R A M n (matrixCornerRestriction r n ψ) := by
  ext x
  simp only [matrixCornerRestriction_apply, hochschildCoboundary_apply]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) ?_
  simpa only [matrixCornerRestriction_apply, hochschildCoface_apply] using
    DFunLike.congr_fun (matrixCornerRestriction_hochschildCoface r n i ψ) x

end CornerCoboundary

/-! ### Abstract prism alternating-sum identity -/

section PrismSum

/-- **Combinatorial prism cancellation.** Let `F : Fin (m + 2) → Fin (m + 3) → G` and
`G' : Fin (m + 2) → Fin (m + 1) → G` satisfy the prism face relations:
* `F (k' + 1) j = G' j k'` for `j ≤ k'`,
* `F k' (j + 1) = G' j k'` for `k' < j`, and
* `F (l + 1) (l + 1) = F l (l + 1)` along the adjacent interior diagonals.

Then the signed sum of `G'` plus the signed sum of `F` collapses to the two boundary terms
`F 0 0 - F (m + 1) (m + 2)`. -/
private theorem prism_alternating_sum_eq_sub {G : Type*} [AddCommGroup G] {m : ℕ}
    (F : Fin (m + 2) → Fin (m + 3) → G) (G' : Fin (m + 2) → Fin (m + 1) → G)
    (h_lt : ∀ (j : Fin (m + 2)) (k' : Fin (m + 1)), (j : ℕ) ≤ k' → F k'.succ j.castSucc = G' j k')
    (h_gt : ∀ (j : Fin (m + 2)) (k' : Fin (m + 1)), (k' : ℕ) < j → F k'.castSucc j.succ = G' j k')
    (h_diag : ∀ l : Fin (m + 1), F l.succ l.succ.castSucc = F l.castSucc l.castSucc.succ) :
    (∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) • ∑ k' : Fin (m + 1), (-1 : ℤ) ^ (k' : ℕ) • G' j k') +
        (∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) • F k i) =
      F 0 0 - F (Fin.last (m + 1)) (Fin.last (m + 2)) := by
  simp only [Finset.smul_sum, smul_smul, ← pow_add, ← Finset.sum_product', Finset.univ_product_univ]
  let d₁Emb : Fin (m + 2) ↪ Fin (m + 2) × Fin (m + 3) :=
    ⟨fun k ↦ (k, k.castSucc), fun _ _ h ↦ (Prod.mk.inj h).1⟩
  let d₂Emb : Fin (m + 2) ↪ Fin (m + 2) × Fin (m + 3) :=
    ⟨fun k ↦ (k, k.succ), fun _ _ h ↦ (Prod.mk.inj h).1⟩
  let offFun : Fin (m + 2) × Fin (m + 1) → Fin (m + 2) × Fin (m + 3) :=
    fun jk ↦ if (jk.1 : ℕ) ≤ jk.2 then (jk.2.succ, jk.1.castSucc) else (jk.2.castSucc, jk.1.succ)
  have hoffInj : Function.Injective offFun := by
    rintro ⟨j₁, k₁⟩ ⟨j₂, k₂⟩ h
    dsimp only [offFun] at h
    split_ifs at h with h₁ h₂ h₂
    · obtain ⟨hk, hj⟩ := Prod.mk.inj h
      exact Prod.ext (Fin.castSucc_inj.1 hj) (Fin.succ_inj.1 hk)
    · obtain ⟨hk, hj⟩ := Prod.mk.inj h
      exfalso
      have hk' := congrArg Fin.val hk
      have hj' := congrArg Fin.val hj
      simp only [Fin.val_succ, Fin.val_castSucc] at hk' hj'
      omega
    · obtain ⟨hk, hj⟩ := Prod.mk.inj h
      exfalso
      have hk' := congrArg Fin.val hk
      have hj' := congrArg Fin.val hj
      simp only [Fin.val_succ, Fin.val_castSucc] at hk' hj'
      omega
    · obtain ⟨hk, hj⟩ := Prod.mk.inj h
      exact Prod.ext (Fin.succ_inj.1 hj) (Fin.castSucc_inj.1 hk)
  let offEmb : Fin (m + 2) × Fin (m + 1) ↪ Fin (m + 2) × Fin (m + 3) := ⟨offFun, hoffInj⟩
  let D₁ := Finset.univ.map d₁Emb
  let D₂ := Finset.univ.map d₂Emb
  let Off := Finset.univ.map offEmb
  have hdisj₁₂ : Disjoint D₁ D₂ := by
    rw [Finset.disjoint_left]
    rintro _ h₁ h₂
    obtain ⟨k₁, -, rfl⟩ := Finset.mem_map.1 h₁
    obtain ⟨k₂, -, h⟩ := Finset.mem_map.1 h₂
    obtain ⟨rfl, hi⟩ := Prod.mk.inj h
    exact absurd (congrArg Fin.val hi) (by simp)
  have hdisjOff : Disjoint (D₁ ∪ D₂) Off := by
    rw [Finset.disjoint_left]
    rintro _ h₁₂ hoff
    obtain ⟨⟨j, k'⟩, -, rfl⟩ := Finset.mem_map.1 hoff
    rcases Finset.mem_union.1 h₁₂ with h₁ | h₂
    · obtain ⟨k, -, hk⟩ := Finset.mem_map.1 h₁
      dsimp only [d₁Emb, offEmb, offFun, Function.Embedding.coeFn_mk] at hk
      split_ifs at hk with hjk <;>
        (obtain ⟨hk₁, hk₂⟩ := Prod.mk.inj hk
         have e₁ := congrArg Fin.val hk₁
         have e₂ := congrArg Fin.val hk₂
         simp only [Fin.val_succ, Fin.val_castSucc] at e₁ e₂
         omega)
    · obtain ⟨k, -, hk⟩ := Finset.mem_map.1 h₂
      dsimp only [d₂Emb, offEmb, offFun, Function.Embedding.coeFn_mk] at hk
      split_ifs at hk with hjk <;>
        (obtain ⟨hk₁, hk₂⟩ := Prod.mk.inj hk
         have e₁ := congrArg Fin.val hk₁
         have e₂ := congrArg Fin.val hk₂
         simp only [Fin.val_succ, Fin.val_castSucc] at e₁ e₂
         omega)
  have hunion : (D₁ ∪ D₂) ∪ Off = Finset.univ := by
    ext ⟨k, i⟩
    simp only [Finset.mem_univ, iff_true, Finset.mem_union, D₁, D₂, Off, Finset.mem_map,
      Finset.mem_univ, true_and, d₁Emb, d₂Emb, offEmb, offFun, Function.Embedding.coeFn_mk]
    obtain hik | rfl | rfl | hki :
        (i : ℕ) < k ∨ i = k.castSucc ∨ i = k.succ ∨ (k : ℕ) + 1 < i := by
      rcases lt_trichotomy (i : ℕ) k with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Fin.ext h))
      · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
        · exact Or.inr (Or.inr (Or.inl (Fin.ext h'.symm)))
        · exact Or.inr (Or.inr (Or.inr h'))
    · right
      refine ⟨(⟨i, by omega⟩, ⟨(k : ℕ) - 1, by omega⟩), ?_⟩
      have hle : (i : ℕ) ≤ (k : ℕ) - 1 := by omega
      simp only [hle, ↓reduceIte]
      exact Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext rfl)
    · exact Or.inl (Or.inl ⟨k, rfl⟩)
    · exact Or.inl (Or.inr ⟨k, rfl⟩)
    · right
      refine ⟨(⟨(i : ℕ) - 1, by omega⟩, ⟨k, by omega⟩), ?_⟩
      have hnle : ¬ ((i : ℕ) - 1 ≤ k) := by omega
      simp only [hnle, ↓reduceIte]
      exact Prod.ext (Fin.ext rfl) (Fin.ext (by dsimp; omega))
  rw [← hunion, Finset.sum_union hdisjOff, Finset.sum_union hdisj₁₂]
  have hsumOff :
      (∑ x ∈ Off, (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ)) • F x.1 x.2) =
        -∑ jk : Fin (m + 2) × Fin (m + 1),
          (-1 : ℤ) ^ ((jk.1 : ℕ) + (jk.2 : ℕ)) • G' jk.1 jk.2 := by
    rw [Finset.sum_map, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ⟨j, k'⟩ _ ↦ ?_
    dsimp only [offEmb, offFun, Function.Embedding.coeFn_mk]
    split_ifs with hjk
    · rw [h_lt j k' hjk, Fin.val_succ, Fin.val_castSucc, ← neg_smul]
      congr 1
      ring
    · rw [h_gt j k' (Nat.lt_of_not_ge hjk), Fin.val_castSucc, Fin.val_succ, ← neg_smul]
      congr 1
      ring
  have hd₁ (k : Fin (m + 2)) : d₁Emb k = (k, k.castSucc) := rfl
  have hsumD₁ :
      (∑ x ∈ D₁, (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ)) • F x.1 x.2) =
        F 0 0 + ∑ l : Fin (m + 1), F l.succ l.succ.castSucc := by
    rw [Finset.sum_map]
    have hpow (k : Fin (m + 2)) :
        (-1 : ℤ) ^ ((k : ℕ) + (k.castSucc : ℕ)) • F k k.castSucc = F k k.castSucc := by
      rw [Fin.val_castSucc, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
    simp only [hd₁, hpow]
    rw [Fin.sum_univ_succ, Fin.castSucc_zero]
  have hd₂ (k : Fin (m + 2)) : d₂Emb k = (k, k.succ) := rfl
  have hsumD₂ :
      (∑ x ∈ D₂, (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ)) • F x.1 x.2) =
        -(∑ l : Fin (m + 1), F l.castSucc l.castSucc.succ) -
          F (Fin.last (m + 1)) (Fin.last (m + 2)) := by
    rw [Finset.sum_map]
    have hpow (k : Fin (m + 2)) :
        (-1 : ℤ) ^ ((k : ℕ) + (k.succ : ℕ)) • F k k.succ = -F k k.succ := by
      rw [Fin.val_succ, ← add_assoc, ← two_mul, pow_add, pow_mul, neg_one_sq, one_pow, one_mul,
        pow_one, neg_one_smul]
    simp only [hd₂, hpow, Finset.sum_neg_distrib]
    rw [Fin.sum_univ_castSucc, Fin.succ_last, neg_add_rev, sub_eq_add_neg, add_comm]
  rw [hsumOff, hsumD₁, hsumD₂, Finset.sum_congr rfl fun l _ ↦ h_diag l]
  abel

end PrismSum

/-! ### The prism cochain homotopy -/

section PrismHomotopy

variable {R A M ι : Type*} [Semiring R] [NonAssocSemiring A] [Module R A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M] [DecidableEq ι] [Fintype ι]

private theorem insertNth_const_below {m : ℕ} {β : Type*} {i j : Fin (m + 1)} (h : j < i)
    (x : β) (p : Fin m → β) :
    Fin.insertNth (α := fun _ ↦ β) i x p j = p (j.castPred (Fin.ne_last_of_lt h)) := by
  conv_lhs => rw [← Fin.succAbove_castPred_of_lt i j h]
  exact Fin.insertNth_apply_succAbove (α := fun _ ↦ β) i x p _

private theorem insertNth_const_above {m : ℕ} {β : Type*} {i j : Fin (m + 1)} (h : i < j)
    (x : β) (p : Fin m → β) :
    Fin.insertNth (α := fun _ ↦ β) i x p j = p (j.pred (Fin.ne_zero_of_lt h)) := by
  conv_lhs => rw [← Fin.succAbove_pred_of_lt i j h]
  exact Fin.insertNth_apply_succAbove (α := fun _ ↦ β) i x p _

/-- Auxiliary linear map inserting a fixed matrix `y` into slot `p` of a multilinear cochain. -/
private def insertConstMultilinearMap {n : ℕ} (p : Fin (n + 2)) (y : Matrix ι ι A) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M where
  toFun ψ := MultilinearMap.mk' (fun X ↦ ψ (p.insertNth y X))
    (fun X i u v ↦ by
      rw [Fin.insertNth_update, Fin.insertNth_update, Fin.insertNth_update, ψ.map_update_add])
    (fun X i c u ↦ by
      rw [Fin.insertNth_update, Fin.insertNth_update, ψ.map_update_smul, RingHom.id_apply])
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq ι] [Fintype ι] in
private theorem insertConstMultilinearMap_apply {n : ℕ} (p : Fin (n + 2)) (y : Matrix ι ι A)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (X : Fin (n + 1) → Matrix ι ι A) :
    insertConstMultilinearMap p y ψ X = ψ (p.insertNth y X) :=
  rfl

/-- In slot `t` of an `n`-cochain argument tuple, the `k`-th prism step along the index path `q`
replaces `X₀` by `E_{q₀, r}(X₀(q₀, q₁))`, replaces `Xₜ` (`1 ≤ t ≤ k`) by
`E_{r, r}(Xₜ(qₜ, q_{t+1}))`, and leaves `Xₜ` (`t > k`) unchanged. -/
private def prismEntryLinearMap (R : Type*) [Semiring R] [Module R A] (r : ι) {n : ℕ}
    (k : Fin (n + 1)) (q : Fin ((k : ℕ) + 2) → ι) (t : Fin (n + 1)) :
    Matrix ι ι A →ₗ[R] Matrix ι ι A :=
  if ht : (t : ℕ) ≤ k then
    Matrix.singleLinearMap R (if (t : ℕ) = 0 then q 0 else r) r ∘ₗ
      Matrix.entryLinearMap R A (q ⟨t, by omega⟩) (q ⟨(t : ℕ) + 1, by omega⟩)
  else LinearMap.id

/-- The `(n + 2)`-tuple `(E_{q₀, r}(X₀(q₀, q₁)), E_{r, r}(X₁(q₁, q₂)), …, E_{r, q_{k+1}}(1),
X_{k+1}, …, Xₙ)` appearing in the `k`-th step of the prism homotopy. -/
private def prismTuple (r : ι) {n : ℕ} (k : Fin (n + 1)) (q : Fin ((k : ℕ) + 2) → ι)
    (X : Fin (n + 1) → Matrix ι ι A) : Fin (n + 2) → Matrix ι ι A :=
  k.succ.insertNth (Matrix.single r (q (Fin.last ((k : ℕ) + 1))) 1) fun t ↦
    if ht : (t : ℕ) ≤ k then
      Matrix.single (if (t : ℕ) = 0 then q 0 else r) r
        (X t (q ⟨t, by omega⟩) (q ⟨(t : ℕ) + 1, by omega⟩))
    else X t

omit [Fintype ι] in
private theorem prismTuple_apply_of_le (r : ι) {n : ℕ} (k : Fin (n + 1))
    (q : Fin ((k : ℕ) + 2) → ι) (X : Fin (n + 1) → Matrix ι ι A) {s : Fin (n + 2)}
    (hsk : (s : ℕ) ≤ k) :
    prismTuple r k q X s =
      Matrix.single (if (s : ℕ) = 0 then q 0 else r) r
        (X ⟨s, by omega⟩ (q ⟨s, by omega⟩) (q ⟨(s : ℕ) + 1, by omega⟩)) := by
  have hs : s < k.succ := Fin.lt_def.2 (by simp; omega)
  rw [prismTuple, insertNth_const_below hs]
  simp only [Fin.coe_castPred, hsk, ↓reduceDIte]
  rfl

omit [Fintype ι] in
private theorem prismTuple_apply_zero (r : ι) {n : ℕ} (k : Fin (n + 1))
    (q : Fin ((k : ℕ) + 2) → ι) (X : Fin (n + 1) → Matrix ι ι A) :
    prismTuple r k q X 0 = Matrix.single (q 0) r (X 0 (q 0) (q ⟨1, by omega⟩)) := by
  rw [prismTuple_apply_of_le r k q X (Nat.zero_le _)]
  simp only [Fin.val_zero, ↓reduceIte, zero_add]
  rfl

omit [Fintype ι] in
private theorem prismTuple_apply_succ_same (r : ι) {n : ℕ} (k : Fin (n + 1))
    (q : Fin ((k : ℕ) + 2) → ι) (X : Fin (n + 1) → Matrix ι ι A) :
    prismTuple r k q X k.succ = Matrix.single r (q (Fin.last ((k : ℕ) + 1))) 1 := by
  rw [prismTuple, Fin.insertNth_apply_same]

omit [Fintype ι] in
private theorem prismTuple_apply_of_gt (r : ι) {n : ℕ} (k : Fin (n + 1))
    (q : Fin ((k : ℕ) + 2) → ι) (X : Fin (n + 1) → Matrix ι ι A) {s : Fin (n + 2)}
    (hks : (k : ℕ) + 1 < s) :
    prismTuple r k q X s = X ⟨(s : ℕ) - 1, by omega⟩ := by
  have hs : k.succ < s := Fin.lt_def.2 hks
  rw [prismTuple, insertNth_const_above hs]
  have hpred : s.pred (Fin.ne_zero_of_lt hs) = ⟨(s : ℕ) - 1, by omega⟩ := by
    ext
    simp [Fin.val_pred]
  rw [hpred]
  have hnotle : ¬ (((s : ℕ) - 1) ≤ k) := by omega
  simp [hnotle]

/-- The `k`-th unsigned step of the prism homotopy on matrix Hochschild cochains. -/
private def matrixHochschildHomotopyStep (r : ι) (n : ℕ) (k : Fin (n + 1)) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M where
  toFun ψ := ∑ q : Fin ((k : ℕ) + 2) → ι,
    (insertConstMultilinearMap k.succ
        (Matrix.single r (q (Fin.last ((k : ℕ) + 1))) 1) ψ).compLinearMap
      (prismEntryLinearMap R r k q)
  map_add' ψ χ := by
    ext X
    simp [insertConstMultilinearMap, MultilinearMap.compLinearMap_apply, Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext X
    simp [insertConstMultilinearMap, MultilinearMap.compLinearMap_apply, Finset.smul_sum]

/-- **Prism cochain homotopy for matrix Hochschild cochains.** Sends an `(n + 1)`-cochain `ψ` on
`Matrix ι ι A` to the `n`-cochain `Hₙ ψ` witnessing that `(corner_r ψ)#Tr` is cochain homotopic to
`ψ`. -/
def matrixHochschildHomotopy (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M :=
  ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • matrixHochschildHomotopyStep r n k

private theorem matrixHochschildHomotopy_eq_sum_prismTuple (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (X : Fin (n + 1) → Matrix ι ι A) :
    matrixHochschildHomotopy r n ψ X =
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        ∑ q : Fin ((k : ℕ) + 2) → ι, ψ (prismTuple r k q X) := by
  simp only [matrixHochschildHomotopy, LinearMap.sum_apply, LinearMap.smul_apply,
    sum_apply, smul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ congrArg ((-1 : ℤ) ^ (k : ℕ) • ·) ?_
  rw [matrixHochschildHomotopyStep]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, sum_apply]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [MultilinearMap.compLinearMap_apply, insertConstMultilinearMap_apply, prismTuple]
  congr 2
  funext t
  dsimp only [prismEntryLinearMap]
  split_ifs <;> rfl

/-- Explicit formula for the prism cochain homotopy on a tuple of matrices. -/
theorem matrixHochschildHomotopy_apply (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (X : Fin (n + 1) → Matrix ι ι A) :
    matrixHochschildHomotopy r n ψ X =
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        ∑ q : Fin ((k : ℕ) + 2) → ι,
          ψ (k.succ.insertNth (Matrix.single r (q (Fin.last ((k : ℕ) + 1))) 1) fun t ↦
            if ht : (t : ℕ) ≤ k then
              Matrix.single (if (t : ℕ) = 0 then q 0 else r) r
                (X t (q ⟨t, by omega⟩) (q ⟨(t : ℕ) + 1, by omega⟩))
            else X t) :=
  matrixHochschildHomotopy_eq_sum_prismTuple r n ψ X

/-! ### Face identities of the prism tuple -/

/-- Multiplying the row-`r` unit `E_{r, a}(1)` on the right by a matrix `Y` expands over the columns
of row `a` of `Y`. -/
private theorem single_one_mul_eq_sum_single (r a : ι) (Y : Matrix ι ι A) :
    Matrix.single r a (1 : A) * Y = ∑ c : ι, Matrix.single r c (Y a c) := by
  ext u v
  rw [Matrix.sum_apply]
  by_cases hur : u = r
  · subst hur
    rw [Matrix.single_mul_apply_same, one_mul, Finset.sum_eq_single v]
    · simp
    · intro c _ hcv
      exact Matrix.single_apply_of_col_ne u u hcv (Y a c)
    · intro hv
      exact absurd (Finset.mem_univ v) hv
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hur, Finset.sum_eq_zero]
    intro c _
    exact Matrix.single_apply_of_row_ne (Ne.symm hur) c v (Y a c)

/-- Multiplying a matrix `Y` on the right by `E_{a, r}(z)` expands over the rows of column `a` of
`Y`. -/
private theorem mul_single_eq_sum_single (Y : Matrix ι ι A) (a r : ι) (z : A) :
    Y * Matrix.single a r z = ∑ u : ι, Matrix.single u r (Y u a * z) := by
  ext u v
  rw [Matrix.sum_apply]
  by_cases hvr : v = r
  · subst hvr
    rw [Matrix.mul_single_apply_same, Finset.sum_eq_single u]
    · simp
    · intro w _ hwu
      exact Matrix.single_apply_of_row_ne hwu v v (Y w a * z)
    · intro hu
      exact absurd (Finset.mem_univ u) hu
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hvr, Finset.sum_eq_zero]
    intro w _
    exact Matrix.single_apply_of_col_ne w u (Ne.symm hvr) (Y w a * z)

omit [SMulCommClass R R M] in
/-- **Initial boundary face (`k = 0, i = 0`).** Contracting the first two entries of `prismTuple` at
`k = 0` reconstructs `X₀` from its matrix units and yields `ψ X`. -/
private theorem sum_hochschildFace_zero_prismTuple_zero (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (X : Fin (n + 1) → Matrix ι ι A) :
    (∑ q : Fin (((0 : Fin (n + 1)) : ℕ) + 2) → ι,
        ψ (hochschildFace 0 (prismTuple r 0 q X))) = ψ X := by
  let i₁ : Fin (((0 : Fin (n + 1)) : ℕ) + 2) := ⟨1, by simp⟩
  have htuple (q : Fin (((0 : Fin (n + 1)) : ℕ) + 2) → ι) :
      hochschildFace 0 (prismTuple r 0 q X) =
        Function.update X 0 (Matrix.single (q 0) (q i₁) (X 0 (q 0) (q i₁))) := by
    rw [← Fin.castSucc_zero, hochschildFace_castSucc]
    funext s
    cases s using Fin.cases with
    | zero =>
      rw [Function.update_self, Fin.contractNth_apply_of_eq _ _ _ _ rfl, Fin.castSucc_zero,
        prismTuple_apply_zero, prismTuple_apply_succ_same, Matrix.single_mul_single_same, mul_one]
      have hlast : (Fin.last (((0 : Fin (n + 1)) : ℕ) + 1)) = i₁ := by
        ext
        simp [i₁]
      rw [hlast]
    | succ t =>
      rw [Function.update_of_ne (Fin.succ_ne_zero t),
        Fin.contractNth_apply_of_gt _ _ _ _ (Fin.succ_pos t),
        prismTuple_apply_of_gt r 0 q X (by simp)]
      rfl
  simp_rw [htuple]
  let e₂ : (ι × ι) ≃ (Fin (((0 : Fin (n + 1)) : ℕ) + 2) → ι) :=
    { toFun := fun ab t ↦ if (t : ℕ) = 0 then ab.1 else ab.2
      invFun := fun q ↦ (q 0, q i₁)
      left_inv := fun ⟨a, b⟩ ↦ by simp [i₁]
      right_inv := fun q ↦ by
        funext t
        have ht : (t : ℕ) = 0 ∨ (t : ℕ) = 1 := by
          have := t.2
          simp at this
          omega
        rcases ht with ht0 | ht1
        · have ht0' : t = 0 := Fin.ext (by simpa using ht0)
          subst ht0'
          simp
        · have ht1' : t = i₁ := Fin.ext ht1
          subst ht1'
          simp [i₁] }
  rw [← e₂.sum_comp, Fintype.sum_prod_type]
  have he₂_0 (a b : ι) : e₂ (a, b) 0 = a := by
    change (if ((0 : Fin (((0 : Fin (n + 1)) : ℕ) + 2)) : ℕ) = 0 then a else b) = a
    simp
  have he₂_1 (a b : ι) : e₂ (a, b) i₁ = b := by
    change (if (i₁ : ℕ) = 0 then a else b) = b
    simp [i₁]
  simp only [he₂_0, he₂_1]
  simp_rw [← ψ.map_update_sum]
  rw [← Matrix.matrix_eq_sum_single (X 0), Function.update_eq_self]

/-- **Final boundary face (`k = n, i = n + 1`).** Contracting the last and first entries of
`prismTuple` at `k = n` closes the index path `q` and yields `(corner_r ψ)#Tr (X)`. -/
private theorem sum_hochschildFace_last_prismTuple_last (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (X : Fin (n + 1) → Matrix ι ι A) :
    (∑ q : Fin ((Fin.last n : ℕ) + 2) → ι,
        ψ (hochschildFace (Fin.last (n + 1)) (prismTuple r (Fin.last n) q X))) =
      matrixCochainExtension ι n (matrixCornerRestriction r n ψ) X := by
  change (∑ q : Fin (n + 2) → ι,
      ψ (hochschildFace (Fin.last (n + 1)) (prismTuple r (Fin.last n) q X))) = _
  rw [← (Fin.snocEquiv fun _ : Fin (n + 2) ↦ ι).sum_comp, Fintype.sum_prod_type, Finset.sum_comm,
    matrixCochainExtension_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.sum_eq_single (p 0)]
  · rw [matrixCornerRestriction_apply]
    congr 1
    funext s
    have hsnoc_succ (t : Fin (n + 1)) :
        (Fin.snoc p (p 0) : Fin (n + 2) → ι) t.succ = p (finRotate (n + 1) t) := by
      by_cases ht : t = Fin.last n
      · subst ht
        simp
      · have heq : t.succ = (finRotate (n + 1) t).castSucc :=
          Fin.ext (coe_finRotate_of_ne_last ht).symm
        rw [heq, Fin.snoc_castSucc]
    rw [hochschildFace_last]
    cases s using Fin.cases with
    | zero =>
      rw [Fin.cons_zero, ← Fin.succ_last, prismTuple_apply_succ_same, prismTuple_apply_zero,
        Fin.snocEquiv_apply]
      dsimp only [Fin.val_last]
      have h0 : (Fin.snoc p (p 0) : Fin (n + 2) → ι) 0 = p 0 := by simp
      have hlast : (Fin.snoc p (p 0) : Fin (n + 2) → ι) (Fin.last (n + 1)) = p 0 := by simp
      have h1 : (Fin.snoc p (p 0) : Fin (n + 2) → ι) ⟨1, by simp⟩ =
          p (finRotate (n + 1) 0) := by
        simpa using hsnoc_succ 0
      rw [hlast, h0, h1, Matrix.single_mul_single_same, one_mul]
    | succ t =>
      rw [Fin.cons_succ, Fin.snocEquiv_apply,
        prismTuple_apply_of_le r (Fin.last n) _ X (by simp)]
      dsimp only
      have hne0 : (t.castSucc.succ : ℕ) ≠ 0 := by simp
      have ht₁ : (⟨(t.castSucc.succ : ℕ), by simp⟩ : Fin (n + 1)) = t.succ := by ext; simp
      have ht₂ : (⟨(t.castSucc.succ : ℕ), by simp⟩ : Fin (n + 2)) = t.succ.castSucc := by
        ext; simp
      have ht₃ : (⟨(t.castSucc.succ : ℕ) + 1, by simp⟩ : Fin (n + 2)) = t.succ.succ := by
        ext; simp
      simp only [hne0, ↓reduceIte]
      rw [ht₁, ht₂, ht₃, Fin.snoc_castSucc, hsnoc_succ t.succ]
  · intro c _ hc
    refine ψ.map_coord_zero 0 ?_
    rw [hochschildFace_last, Fin.cons_zero, Fin.snocEquiv_apply, ← Fin.succ_last,
      prismTuple_apply_succ_same, prismTuple_apply_zero]
    dsimp only [Fin.val_last]
    have h0 : (Fin.snoc p c : Fin (n + 2) → ι) 0 = p 0 := by simp
    have hlast : (Fin.snoc p c : Fin (n + 2) → ι) (Fin.last (n + 1)) = c := by simp
    rw [hlast, h0]
    simp [hc]
  · intro hp
    exact absurd (Finset.mem_univ (p 0)) hp

omit [SMulCommClass R R M] in
/-- **Adjacent interior diagonal cancellation (`i = l + 1`, `k = l + 1` vs `k = l`).** -/
private theorem sum_hochschildFace_diag_prismTuple (r : ι) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ Matrix ι ι A) M)
    (X : Fin (m + 2) → Matrix ι ι A) (l : Fin (m + 1)) :
    (∑ q : Fin ((l.succ : ℕ) + 2) → ι,
        ψ (hochschildFace l.succ.castSucc (prismTuple r l.succ q X))) =
      ∑ q' : Fin ((l.castSucc : ℕ) + 2) → ι,
        ψ (hochschildFace l.castSucc.succ (prismTuple r l.castSucc q' X)) := by
  change (∑ q : Fin ((l : ℕ) + 3) → ι,
      ψ (hochschildFace l.succ.castSucc (prismTuple r l.succ q X))) =
    ∑ q' : Fin ((l : ℕ) + 2) → ι,
      ψ (hochschildFace l.castSucc.succ (prismTuple r l.castSucc q' X))
  rw [← (Fin.snocEquiv fun _ : Fin ((l : ℕ) + 3) ↦ ι).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun q' _ ↦ ?_
  have hrhs : hochschildFace l.castSucc.succ (prismTuple r l.castSucc q' X) =
      Function.update (hochschildFace l.castSucc.succ (prismTuple r l.castSucc q' X)) l.succ
        (∑ c : ι, Matrix.single r c (X l.succ (q' (Fin.last ((l : ℕ) + 1))) c)) := by
    rw [eq_comm, Function.update_eq_self_iff, Fin.succ_castSucc, hochschildFace_castSucc,
      Fin.contractNth_apply_of_eq _ _ _ _ rfl, ← Fin.succ_castSucc, prismTuple_apply_succ_same,
      prismTuple_apply_of_gt r l.castSucc q' X (by simp), single_one_mul_eq_sum_single]
    rfl
  rw [hrhs, ψ.map_update_sum]
  refine Finset.sum_congr rfl fun c _ ↦ congrArg ψ ?_
  funext s
  rw [Fin.snocEquiv_apply, Fin.succ_castSucc, hochschildFace_castSucc]
  dsimp only
  rcases lt_trichotomy s l.succ with hs | rfl | hs
  · have hsl : (s : ℕ) ≤ l := Nat.lt_succ_iff.1 hs
    rw [Function.update_of_ne hs.ne, hochschildFace_castSucc,
      Fin.contractNth_apply_of_lt _ _ _ _ hs, Fin.contractNth_apply_of_lt _ _ _ _ hs,
      prismTuple_apply_of_le r l.succ _ X (by simp; omega),
      prismTuple_apply_of_le r l.castSucc _ X (by simpa using hsl)]
    have h0 : (Fin.snoc q' c : Fin ((l : ℕ) + 3) → ι) 0 = q' 0 := by simp
    have ha : (Fin.snoc q' c : Fin ((l : ℕ) + 3) → ι) ⟨(s.castSucc : ℕ), by simp; omega⟩ =
        q' ⟨(s.castSucc : ℕ), by simp; omega⟩ := by
      have heq : (⟨(s.castSucc : ℕ), by simp; omega⟩ : Fin ((l : ℕ) + 3)) =
          (⟨(s.castSucc : ℕ), by simp; omega⟩ : Fin ((l : ℕ) + 2)).castSucc := by ext; simp
      rw [heq, Fin.snoc_castSucc]
    have hb : (Fin.snoc q' c : Fin ((l : ℕ) + 3) → ι) ⟨(s.castSucc : ℕ) + 1, by simp; omega⟩ =
        q' ⟨(s.castSucc : ℕ) + 1, by simp; omega⟩ := by
      have heq : (⟨(s.castSucc : ℕ) + 1, by simp; omega⟩ : Fin ((l : ℕ) + 3)) =
          (⟨(s.castSucc : ℕ) + 1, by simp; omega⟩ : Fin ((l : ℕ) + 2)).castSucc := by ext; simp
      rw [heq, Fin.snoc_castSucc]
    rw [h0, ha, hb]
  · rw [Function.update_self, Fin.contractNth_apply_of_eq _ _ _ _ rfl,
      prismTuple_apply_of_le r l.succ _ X (by simp), prismTuple_apply_succ_same]
    have hne0 : (l.succ.castSucc : ℕ) ≠ 0 := by simp
    have ha : (Fin.snoc q' c : Fin ((l : ℕ) + 3) → ι) ⟨(l.succ.castSucc : ℕ), by simp⟩ =
        q' (Fin.last ((l : ℕ) + 1)) := by
      have heq : (⟨(l.succ.castSucc : ℕ), by simp⟩ : Fin ((l : ℕ) + 3)) =
          (Fin.last ((l : ℕ) + 1)).castSucc := by ext; simp
      rw [heq, Fin.snoc_castSucc]
    have hb : (Fin.snoc q' c : Fin ((l : ℕ) + 3) → ι) ⟨(l.succ.castSucc : ℕ) + 1, by simp⟩ = c := by
      have heq : (⟨(l.succ.castSucc : ℕ) + 1, by simp⟩ : Fin ((l : ℕ) + 3)) =
          Fin.last ((l : ℕ) + 2) := by ext; simp
      rw [heq, Fin.snoc_last]
    have hc' : (Fin.snoc q' c : Fin ((l : ℕ) + 3) → ι) (Fin.last ((l.succ : ℕ) + 1)) = c := by
      have heq : (Fin.last ((l.succ : ℕ) + 1) : Fin ((l : ℕ) + 3)) = Fin.last ((l : ℕ) + 2) := by
        ext; simp
      rw [heq, Fin.snoc_last]
    have hidx : (⟨(l.succ.castSucc : ℕ), by simp; omega⟩ : Fin (m + 2)) = l.succ := by ext; simp
    simp only [hne0, ↓reduceIte]
    rw [ha, hb, hc', hidx, Matrix.single_mul_single_same, mul_one]
  · have hsl : (l : ℕ) + 1 < s := by simpa [Fin.lt_def] using hs
    rw [Function.update_of_ne hs.ne', hochschildFace_castSucc,
      Fin.contractNth_apply_of_gt _ _ _ _ hs, Fin.contractNth_apply_of_gt _ _ _ _ hs,
      prismTuple_apply_of_gt r l.succ _ X (by simp; omega),
      prismTuple_apply_of_gt r l.castSucc _ X (by simp; omega)]

omit [SMulCommClass R R M] in
/-- **Lower triangle (`j ≤ k'`).** Contracting two matrix-unit slots of `prismTuple` sums over the
intermediate matrix index to match `prismTuple` applied to `hochschildFace j X`. -/
private theorem sum_hochschildFace_prismTuple_of_le (r : ι) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ Matrix ι ι A) M)
    (X : Fin (m + 2) → Matrix ι ι A) (j : Fin (m + 2)) (k' : Fin (m + 1)) (hjk : (j : ℕ) ≤ k') :
    (∑ q : Fin ((k'.succ : ℕ) + 2) → ι,
        ψ (hochschildFace j.castSucc (prismTuple r k'.succ q X))) =
      ∑ q' : Fin ((k' : ℕ) + 2) → ι, ψ (prismTuple r k' q' (hochschildFace j X)) := by
  let j₀ : Fin (m + 1) := ⟨j, by omega⟩
  have hj : j = j₀.castSucc := Fin.ext rfl
  have hface_eq (t : Fin (m + 1)) :
      hochschildFace j X t = Fin.contractNth j₀.castSucc (· * ·) X t := by
    rw [hj, hochschildFace_castSucc]
  let pIdx : Fin ((k' : ℕ) + 3) := ⟨(j : ℕ) + 1, by omega⟩
  change (∑ q : Fin ((k' : ℕ) + 3) → ι,
      ψ (hochschildFace j.castSucc (prismTuple r k'.succ q X))) = _
  rw [← (Fin.insertNthEquiv (fun _ : Fin ((k' : ℕ) + 3) ↦ ι) pIdx).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun q' _ ↦ ?_
  let rowIdx : ι := if (j : ℕ) = 0 then q' 0 else r
  have hface_j : hochschildFace j X ⟨j, by omega⟩ = X j₀.castSucc * X j₀.succ := by
    have hidx : (⟨(j : ℕ), by omega⟩ : Fin (m + 1)) = j₀ := Fin.ext rfl
    rw [hidx, hface_eq, Fin.contractNth_apply_of_eq _ _ _ _ rfl]
  have hrhs : prismTuple r k' q' (hochschildFace j X) =
      Function.update (prismTuple r k' q' (hochschildFace j X)) j
        (∑ c : ι, Matrix.single rowIdx r
          (X j₀.castSucc (q' ⟨j, by omega⟩) c * X j₀.succ c (q' ⟨(j : ℕ) + 1, by omega⟩))) := by
    rw [eq_comm, Function.update_eq_self_iff, prismTuple_apply_of_le r k' q' _ hjk, hface_j,
      Matrix.mul_apply]
    exact (map_sum (Matrix.singleLinearMap R rowIdx r) _ _).symm
  rw [hrhs, ψ.map_update_sum]
  refine Finset.sum_congr rfl fun c _ ↦ congrArg ψ ?_
  funext s
  rw [Fin.insertNthEquiv_apply, hochschildFace_castSucc]
  dsimp only
  let qIns : Fin ((k' : ℕ) + 3) → ι := pIdx.insertNth c q'
  have hins_lt {t : ℕ} (ht : t ≤ j) (ht1 : t < (k' : ℕ) + 3) (ht2 : t < (k' : ℕ) + 2) :
      qIns ⟨t, ht1⟩ = q' ⟨t, ht2⟩ := by
    have hlt : (⟨t, ht1⟩ : Fin ((k' : ℕ) + 3)) < pIdx := Fin.lt_def.2 (by dsimp [pIdx]; omega)
    dsimp only [qIns]
    rw [insertNth_const_below hlt]
    rfl
  have hins_eq : qIns pIdx = c := Fin.insertNth_apply_same (α := fun _ ↦ ι) pIdx c q'
  have hins_gt {t : ℕ} (ht : (j : ℕ) + 1 < t) (ht1 : t < (k' : ℕ) + 3)
      (ht2 : t - 1 < (k' : ℕ) + 2) :
      qIns ⟨t, ht1⟩ = q' ⟨t - 1, ht2⟩ := by
    have hgt : pIdx < (⟨t, ht1⟩ : Fin ((k' : ℕ) + 3)) := Fin.lt_def.2 ht
    dsimp only [qIns]
    rw [insertNth_const_above hgt]
    congr 1
  have hins0 : qIns 0 = q' 0 := by
    change qIns ⟨0, _⟩ = q' ⟨0, _⟩
    exact hins_lt (Nat.zero_le _) _ _
  change Fin.contractNth j.castSucc (· * ·) (prismTuple r k'.succ qIns X) s = _
  rcases lt_trichotomy s j with hs | hsj | hs
  · rw [Function.update_of_ne hs.ne, Fin.contractNth_apply_of_lt _ _ _ _ hs,
      prismTuple_apply_of_le r k'.succ qIns X (by simp; omega),
      prismTuple_apply_of_le r k' q' _ (by omega)]
    rw [hface_eq,
      Fin.contractNth_apply_of_lt j₀.castSucc (· * ·) X _
        (by dsimp only [j₀]; simp only [Fin.val_castSucc]; exact hs)]
    simp only [Fin.val_castSucc]
    rw [hins0, hins_lt (Nat.le_of_lt hs) _ _, hins_lt hs _ _]
    rfl
  · subst hsj
    rw [Function.update_self, Fin.contractNth_apply_of_eq _ _ _ _ rfl,
      prismTuple_apply_of_le r k'.succ qIns X (by simp; omega),
      prismTuple_apply_of_le r k'.succ qIns X (by simp; omega)]
    have hne : (s.succ : ℕ) ≠ 0 := by simp
    simp only [hne, ↓reduceIte, Fin.val_castSucc]
    rw [hins0, Matrix.single_mul_single_same]
    have h₂ : (⟨(s : ℕ) + 1, by omega⟩ : Fin ((k' : ℕ) + 3)) = pIdx := Fin.ext rfl
    have h₃ : (⟨(s.succ : ℕ), by simp; omega⟩ : Fin ((k' : ℕ) + 3)) = pIdx := by ext; simp [pIdx]
    have h₄ : (⟨(s.succ : ℕ) + 1, by simp; omega⟩ : Fin ((k' : ℕ) + 3)) =
        ⟨(s : ℕ) + 2, by omega⟩ := by ext; simp
    rw [h₂, h₃, h₄, hins_lt le_rfl _ _, hins_eq, hins_gt (by omega) _ (by omega)]
    rfl
  · rw [Function.update_of_ne hs.ne', Fin.contractNth_apply_of_gt _ _ _ _ hs]
    rcases lt_trichotomy (s : ℕ) ((k' : ℕ) + 1) with hsk | hsk | hsk
    · rw [prismTuple_apply_of_le r k'.succ qIns X (by simp; omega),
        prismTuple_apply_of_le r k' q' _ (Nat.le_of_lt_succ hsk)]
      have hne2 : (s : ℕ) ≠ 0 := by omega
      simp only [Fin.val_succ, Nat.add_one_ne_zero, hne2, ↓reduceIte]
      rw [hface_eq,
        Fin.contractNth_apply_of_gt j₀.castSucc (· * ·) X _
          (by dsimp only [j₀]; simp only [Fin.val_castSucc]; exact hs),
        hins_gt (by omega) _ (by omega), hins_gt (by omega) _ (by omega)]
      have heq1 : (⟨(s : ℕ) + 1, by omega⟩ : Fin (m + 2)) =
          (⟨(s : ℕ), by omega⟩ : Fin (m + 1)).succ := Fin.ext rfl
      have heq2 : (⟨(s : ℕ) + 1 - 1, by omega⟩ : Fin ((k' : ℕ) + 2)) = ⟨s, by omega⟩ :=
        Fin.ext (by simp)
      have heq3 : (⟨(s : ℕ) + 1 + 1 - 1, by omega⟩ : Fin ((k' : ℕ) + 2)) =
          ⟨(s : ℕ) + 1, by omega⟩ := Fin.ext (by simp)
      rw [heq1, heq2, heq3]
    · have hs_eq : s = k'.succ := Fin.ext hsk
      subst hs_eq
      rw [prismTuple_apply_succ_same, prismTuple_apply_succ_same]
      have hlast : (Fin.last ((k'.succ : ℕ) + 1)) = ⟨(k' : ℕ) + 2, by omega⟩ := Fin.ext rfl
      rw [hlast, hins_gt (by omega) _ (by omega)]
      congr 2
    · rw [prismTuple_apply_of_gt r k'.succ qIns X (by simp; omega),
        prismTuple_apply_of_gt r k' q' _ hsk]
      rw [hface_eq,
        Fin.contractNth_apply_of_gt j₀.castSucc (· * ·) X _
          (by dsimp only [j₀]; simp only [Fin.val_castSucc]; omega)]
      congr 1
      ext
      simp
      omega

/-- **Upper interior triangle (`k' < j < m + 1`).** Contracting two unsplit matrix slots commutes
pointwise with `prismTuple`. -/
private theorem hochschildFace_prismTuple_of_gt_castSucc (r : ι) {m : ℕ}
    (X : Fin (m + 2) → Matrix ι ι A) (j₀ : Fin (m + 1)) (k' : Fin (m + 1))
    (hkj : (k' : ℕ) < j₀) (q' : Fin ((k' : ℕ) + 2) → ι) :
    hochschildFace j₀.castSucc.succ (prismTuple r k'.castSucc q' X) =
      prismTuple r k' q' (hochschildFace j₀.castSucc X) := by
  funext s
  rw [Fin.succ_castSucc, hochschildFace_castSucc, hochschildFace_castSucc]
  rcases lt_trichotomy (s : ℕ) ((k' : ℕ) + 1) with hsk | hsk | hsk
  · have hsj : s < j₀.succ := Fin.lt_def.2 (by simp; omega)
    rw [Fin.contractNth_apply_of_lt _ _ _ _ hsj,
      prismTuple_apply_of_le r k'.castSucc q' X (by simp; omega),
      prismTuple_apply_of_le r k' q' _ (Nat.le_of_lt_succ hsk)]
    have hsj₀ : (⟨(s : ℕ), by omega⟩ : Fin (m + 1)) < j₀ := Fin.lt_def.2 (by dsimp; omega)
    rw [Fin.contractNth_apply_of_lt _ _ _ _ hsj₀]
    rfl
  · have hs_eq : s = k'.succ := Fin.ext hsk
    subst hs_eq
    have hsj : k'.succ < j₀.succ := Fin.succ_lt_succ_iff.2 hkj
    rw [Fin.contractNth_apply_of_lt _ _ _ _ hsj, ← Fin.succ_castSucc,
      prismTuple_apply_succ_same, prismTuple_apply_succ_same]
    rfl
  · rcases lt_trichotomy s j₀.succ with hsj | rfl | hsj
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ hsj,
        prismTuple_apply_of_gt r k'.castSucc q' X (by simp; omega),
        prismTuple_apply_of_gt r k' q' _ hsk]
      have hsj' : (s : ℕ) < (j₀ : ℕ) + 1 := hsj
      have hsj₀ : (⟨(s : ℕ) - 1, by omega⟩ : Fin (m + 1)) < j₀ :=
        Fin.lt_def.2 (by dsimp; omega)
      rw [Fin.contractNth_apply_of_lt _ _ _ _ hsj₀]
      rfl
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl,
        prismTuple_apply_of_gt r k'.castSucc q' X (by simp; omega),
        prismTuple_apply_of_gt r k'.castSucc q' X (by simp; omega),
        prismTuple_apply_of_gt r k' q' _ hsk]
      have hidx : (⟨(j₀.succ : ℕ) - 1, by omega⟩ : Fin (m + 1)) = j₀ := Fin.ext (by simp)
      rw [hidx, Fin.contractNth_apply_of_eq _ _ _ _ rfl]
      congr 2
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ hsj,
        prismTuple_apply_of_gt r k'.castSucc q' X (by simp; omega),
        prismTuple_apply_of_gt r k' q' _ hsk]
      have hsj' : (j₀ : ℕ) + 1 < (s : ℕ) := hsj
      have hsj₀ : j₀ < (⟨(s : ℕ) - 1, by omega⟩ : Fin (m + 1)) :=
        Fin.lt_def.2 (by dsimp; omega)
      rw [Fin.contractNth_apply_of_gt _ _ _ _ hsj₀]
      congr 1
      ext
      dsimp
      omega

omit [SMulCommClass R R M] in
/-- **Top row (`j = m + 1`, `k' ≤ m`).** The cyclic last face on `prismTuple` swaps the summation
index `q₀` with the intermediate index of `X_{m+1} * X₀`. -/
private theorem sum_hochschildFace_last_prismTuple_castSucc (r : ι) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ Matrix ι ι A) M)
    (X : Fin (m + 2) → Matrix ι ι A) (k' : Fin (m + 1)) :
    (∑ q : Fin ((k'.castSucc : ℕ) + 2) → ι,
        ψ (hochschildFace (Fin.last (m + 2)) (prismTuple r k'.castSucc q X))) =
      ∑ q' : Fin ((k' : ℕ) + 2) → ι,
        ψ (prismTuple r k' q' (hochschildFace (Fin.last (m + 1)) X)) := by
  change (∑ q : Fin ((k' : ℕ) + 2) → ι,
      ψ (hochschildFace (Fin.last (m + 2)) (prismTuple r k'.castSucc q X))) = _
  have hlhs (q : Fin ((k' : ℕ) + 2) → ι) :
      ψ (hochschildFace (Fin.last (m + 2)) (prismTuple r k'.castSucc q X)) =
        ∑ u : ι, ψ (Function.update
          (hochschildFace (Fin.last (m + 2)) (prismTuple r k'.castSucc q X)) 0
          (Matrix.single u r
            (X (Fin.last (m + 1)) u (q 0) * X 0 (q 0) (q ⟨1, by omega⟩)))) := by
    rw [← ψ.map_update_sum]
    congr 1
    rw [eq_comm, Function.update_eq_self_iff, hochschildFace_last, Fin.cons_zero,
      prismTuple_apply_of_gt r k'.castSucc q X (by simp; omega), prismTuple_apply_zero,
      mul_single_eq_sum_single]
    rfl
  have hrhs (q' : Fin ((k' : ℕ) + 2) → ι) :
      ψ (prismTuple r k' q' (hochschildFace (Fin.last (m + 1)) X)) =
        ∑ t : ι, ψ (Function.update
          (prismTuple r k' q' (hochschildFace (Fin.last (m + 1)) X)) 0
          (Matrix.single (q' 0) r
            (X (Fin.last (m + 1)) (q' 0) t * X 0 t (q' ⟨1, by omega⟩)))) := by
    rw [← ψ.map_update_sum]
    congr 1
    rw [eq_comm, Function.update_eq_self_iff, prismTuple_apply_zero, hochschildFace_last,
      Fin.cons_zero, Matrix.mul_apply]
    exact (map_sum (Matrix.singleLinearMap R (q' 0) r) _ _).symm
  simp_rw [hlhs, hrhs]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let swap0 : (Fin ((k' : ℕ) + 2) → ι) × ι ≃ (Fin ((k' : ℕ) + 2) → ι) × ι :=
    { toFun := fun ⟨q, u⟩ ↦ (Function.update q 0 u, q 0)
      invFun := fun ⟨q', t⟩ ↦ (Function.update q' 0 t, q' 0)
      left_inv := fun ⟨q, u⟩ ↦ by simp
      right_inv := fun ⟨q', t⟩ ↦ by simp }
  rw [← swap0.sum_comp]
  refine Finset.sum_congr rfl fun ⟨q, u⟩ _ ↦ congrArg ψ ?_
  dsimp only [swap0, Equiv.coe_fn_mk]
  funext s
  cases s using Fin.cases with
  | zero =>
    rw [Function.update_self, Function.update_self, Function.update_self,
      Function.update_of_ne (by simp : (⟨1, by omega⟩ : Fin ((k' : ℕ) + 2)) ≠ 0)]
  | succ s₀ =>
    rw [Function.update_of_ne (Fin.succ_ne_zero s₀), Function.update_of_ne (Fin.succ_ne_zero s₀),
      hochschildFace_last, Fin.cons_succ]
    rcases lt_trichotomy (s₀ : ℕ) k' with hsk | hsk | hsk
    · rw [prismTuple_apply_of_le r k'.castSucc _ X (by simp; omega),
        prismTuple_apply_of_le r k' _ _ (by simp; omega)]
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_one_ne_zero, ↓reduceIte]
      have h₁ : Function.update q 0 u ⟨(s₀ : ℕ) + 1, by omega⟩ = q ⟨(s₀ : ℕ) + 1, by omega⟩ :=
        Function.update_of_ne (by simp) _ _
      have h₂ : Function.update q 0 u ⟨(s₀ : ℕ) + 1 + 1, by omega⟩ =
          q ⟨(s₀ : ℕ) + 1 + 1, by omega⟩ :=
        Function.update_of_ne (by simp) _ _
      rw [h₁, h₂, hochschildFace_last]
      have hidx : (⟨(s₀ : ℕ) + 1, by omega⟩ : Fin (m + 1)) =
          (⟨(s₀ : ℕ), by omega⟩ : Fin m).succ := Fin.ext rfl
      rw [hidx, Fin.cons_succ]
      rfl
    · have hs₀_eq : s₀ = k' := Fin.ext hsk
      subst hs₀_eq
      rw [prismTuple_apply_succ_same, prismTuple_apply_succ_same]
      simp only [Fin.val_castSucc]
      have hlast : Function.update q 0 u (Fin.last ((s₀ : ℕ) + 1)) = q (Fin.last ((s₀ : ℕ) + 1)) :=
        Function.update_of_ne (Fin.last_pos.ne') _ _
      rw [hlast]
    · rw [prismTuple_apply_of_gt r k'.castSucc _ X (by simp; omega),
        prismTuple_apply_of_gt r k' _ _ (by simp; omega), hochschildFace_last]
      have hidx : (⟨(s₀.succ : ℕ) - 1, by simp; omega⟩ : Fin (m + 1)) =
          (⟨(s₀ : ℕ) - 1, by omega⟩ : Fin m).succ := Fin.ext (by simp; omega)
      rw [hidx, Fin.cons_succ]
      congr 1
      ext
      simp
      omega

/-! ### The cochain homotopy equations -/

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- **Degree-zero homotopy identity:** `H₀ (b ψ) = ψ - (corner_r ψ)#Tr`. -/
theorem matrixHochschildHomotopy_hochschildCoboundary_zero (r : ι)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M) :
    matrixHochschildHomotopy r 0 (hochschildCoboundary R (Matrix ι ι A) M 0 ψ) =
      ψ - matrixCochainExtension ι 0 (matrixCornerRestriction r 0 ψ) := by
  ext X
  rw [sub_apply, matrixHochschildHomotopy_eq_sum_prismTuple, Fin.sum_univ_one]
  have hcob (Y : Fin 2 → Matrix ι ι A) :
      hochschildCoboundary R (Matrix ι ι A) M 0 ψ Y =
        ψ (hochschildFace 0 Y) - ψ (hochschildFace (Fin.last 1) Y) := by
    rw [hochschildCoboundary_apply, Fin.sum_univ_two]
    simp [sub_eq_add_neg]
  simp only [Fin.val_zero, pow_zero, one_smul]
  simp_rw [hcob, Finset.sum_sub_distrib]
  exact congrArg₂ (· - ·) (sum_hochschildFace_zero_prismTuple_zero r ψ X)
    (sum_hochschildFace_last_prismTuple_last r ψ X)

/-- **Positive-degree homotopy identity:** `b (Hₘ ψ) + Hₘ₊₁ (b ψ) = ψ - (corner_r ψ)#Tr`. -/
theorem hochschildCoboundary_matrixHochschildHomotopy_add (r : ι) (m : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ Matrix ι ι A) M) :
    hochschildCoboundary R (Matrix ι ι A) M m (matrixHochschildHomotopy r m ψ) +
        matrixHochschildHomotopy r (m + 1) (hochschildCoboundary R (Matrix ι ι A) M (m + 1) ψ) =
      ψ - matrixCochainExtension ι (m + 1) (matrixCornerRestriction r (m + 1) ψ) := by
  ext X
  rw [add_apply, sub_apply, hochschildCoboundary_apply, matrixHochschildHomotopy_eq_sum_prismTuple]
  simp only [matrixHochschildHomotopy_eq_sum_prismTuple, hochschildCoboundary_apply]
  have hswap (k : Fin (m + 2)) :
      (∑ q : Fin ((k : ℕ) + 2) → ι, ∑ i : Fin (m + 3),
          (-1 : ℤ) ^ (i : ℕ) • ψ (hochschildFace i (prismTuple r k q X))) =
        ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) •
          ∑ q : Fin ((k : ℕ) + 2) → ι, ψ (hochschildFace i (prismTuple r k q X)) := by
    rw [Finset.sum_comm]
    simp only [Finset.smul_sum]
  simp_rw [hswap]
  rw [prism_alternating_sum_eq_sub
    (fun k i ↦ ∑ q : Fin ((k : ℕ) + 2) → ι, ψ (hochschildFace i (prismTuple r k q X)))
    (fun j k' ↦ ∑ q' : Fin ((k' : ℕ) + 2) → ι, ψ (prismTuple r k' q' (hochschildFace j X)))
    (fun j k' hjk ↦ sum_hochschildFace_prismTuple_of_le r ψ X j k' hjk)
    (fun j k' hkj ↦ by
      induction j using Fin.lastCases with
      | last => exact sum_hochschildFace_last_prismTuple_castSucc r ψ X k'
      | cast j₀ =>
        refine Finset.sum_congr rfl fun q' _ ↦ congrArg ψ ?_
        exact hochschildFace_prismTuple_of_gt_castSucc r X j₀ k' hkj q')
    (fun l ↦ sum_hochschildFace_diag_prismTuple r ψ X l)]
  exact congrArg₂ (· - ·) (sum_hochschildFace_zero_prismTuple_zero r ψ X)
    (sum_hochschildFace_last_prismTuple_last r ψ X)

end PrismHomotopy

/-! ### Induced maps and Morita invariance on Hochschild cohomology -/

section Cocycles

variable {R A M ι : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [Fintype ι] {n : ℕ}

/-- Matrix cochain extension maps Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainExtension_mem_hochschildCocycles
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCocycles R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCocycles R (Matrix ι ι A) M n := by
  rw [mem_hochschildCocycles_iff] at hφ ⊢
  rw [← matrixCochainExtension_hochschildCoboundary, hφ, map_zero]

/-- Matrix cochain extension maps Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainExtension_mem_hochschildCoboundaries
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCoboundaries R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, map_zero]
  | succ m =>
    obtain ⟨χ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixCochainExtension ι m χ, (matrixCochainExtension_hochschildCoboundary ι m χ).symm⟩

/-- Corner restriction maps Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCornerRestriction_mem_hochschildCocycles [DecidableEq ι] (r : ι)
    {ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hψ : ψ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    matrixCornerRestriction r n ψ ∈ hochschildCocycles R A M n := by
  rw [mem_hochschildCocycles_iff] at hψ ⊢
  rw [← matrixCornerRestriction_hochschildCoboundary, hψ, map_zero]

/-- Corner restriction maps Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCornerRestriction_mem_hochschildCoboundaries [DecidableEq ι] (r : ι)
    {ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hψ : ψ ∈ hochschildCoboundaries R (Matrix ι ι A) M n) :
    matrixCornerRestriction r n ψ ∈ hochschildCoboundaries R A M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hψ ⊢
    rw [hψ, map_zero]
  | succ m =>
    obtain ⟨χ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hψ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixCornerRestriction r m χ, (matrixCornerRestriction_hochschildCoboundary r m χ).symm⟩

end Cocycles

namespace hochschildCohomology

section NonUnital

variable {R A : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  (M : Type*) [AddCommGroup M] [Module R M]

/-- The map `HHⁿ(A, Hom_R(A, M)) → HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` on Hochschild
cohomology induced by the generalized matrix trace `φ ↦ φ#Tr`. -/
def matrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  desc n (mk R (Matrix ι ι A) M n ∘ₗ
      (matrixCochainExtension ι n).restrict fun _ ↦ matrixCochainExtension_mem_hochschildCocycles)
    fun _ hφ ↦ (mk_eq_zero_iff R (Matrix ι ι A) M n _).2
      (matrixCochainExtension_mem_hochschildCoboundaries hφ)

/-- Matrix extension on Hochschild cohomology sends the class of a cocycle `φ` to the class of
`φ#Tr`. -/
@[simp]
theorem matrixExtension_mk {ι : Type*} [Fintype ι] {n : ℕ} (φ : hochschildCocycles R A M n) :
    matrixExtension M ι n (mk R A M n φ) =
      mk R (Matrix ι ι A) M n
        ⟨matrixCochainExtension ι n φ, matrixCochainExtension_mem_hochschildCocycles φ.2⟩ :=
  desc_mk _ _ _ φ

/-- The map on Hochschild cohomology induced by restricting matrix cochains to the `(r, r)`
diagonal corner. -/
def cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ) :
    hochschildCohomology R (Matrix ι ι A) M n →ₗ[R] hochschildCohomology R A M n :=
  desc n (mk R A M n ∘ₗ
      (matrixCornerRestriction r n).restrict fun _ ↦
        matrixCornerRestriction_mem_hochschildCocycles r)
    fun _ hψ ↦ (mk_eq_zero_iff R A M n _).2
      (matrixCornerRestriction_mem_hochschildCoboundaries r hψ)

/-- Corner restriction on Hochschild cohomology sends the class of a cocycle `ψ` to the class of
its `(r, r)` corner restriction. -/
@[simp]
theorem cornerRestriction_mk {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ}
    (ψ : hochschildCocycles R (Matrix ι ι A) M n) :
    cornerRestriction M r n (mk R (Matrix ι ι A) M n ψ) =
      mk R A M n
        ⟨matrixCornerRestriction r n ψ, matrixCornerRestriction_mem_hochschildCocycles r ψ.2⟩ :=
  desc_mk _ _ _ ψ

/-- Corner restriction is a left inverse to matrix extension on Hochschild cohomology. -/
@[simp]
theorem cornerRestriction_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ)
    (c : hochschildCohomology R A M n) :
    cornerRestriction M r n (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  rw [matrixExtension_mk, cornerRestriction_mk]
  congr 1
  exact Subtype.ext (matrixCornerRestriction_matrixCochainExtension r n φ.1)

/-- Corner restriction composed with matrix extension is the identity on Hochschild cohomology. -/
@[simp]
theorem cornerRestriction_comp_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι)
    (n : ℕ) :
    cornerRestriction (R := R) (A := A) M r n ∘ₗ matrixExtension M ι n = LinearMap.id :=
  LinearMap.ext (cornerRestriction_matrixExtension M r n)

variable {M} in
/-- Matrix extension on Hochschild cohomology is injective for any nonempty finite index type, even
when `A` is nonunital. -/
theorem injective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Injective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.LeftInverse.injective (cornerRestriction_matrixExtension M r n)

end NonUnital

section Unital

variable {R A : Type*} [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  (M : Type*) [AddCommGroup M] [Module R M]

/-- For a unital algebra, matrix extension is a left inverse to corner restriction on Hochschild
cohomology: `(corner_r ψ)#Tr` is cohomologous to `ψ` via the prism homotopy. -/
@[simp]
theorem matrixExtension_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ)
    (c : hochschildCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M r n c) = c := by
  obtain ⟨ψ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n c
  rw [cornerRestriction_mk, matrixExtension_mk, eq_comm, mk_eq_mk_iff]
  have hψ : hochschildCoboundary R (Matrix ι ι A) M n ψ.1 = 0 := mem_hochschildCocycles_iff.1 ψ.2
  cases n with
  | zero =>
    have h0 := matrixHochschildHomotopy_hochschildCoboundary_zero r ψ.1
    rw [hψ, map_zero] at h0
    rw [← h0, hochschildCoboundaries_zero]
    exact Submodule.zero_mem ⊥
  | succ m =>
    have hm := hochschildCoboundary_matrixHochschildHomotopy_add r m ψ.1
    rw [hψ, map_zero, add_zero] at hm
    exact mem_hochschildCoboundaries_succ_iff.2 ⟨matrixHochschildHomotopy r m ψ.1, hm⟩

/-- Matrix extension composed with corner restriction is the identity on Hochschild cohomology. -/
@[simp]
theorem matrixExtension_comp_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι)
    (n : ℕ) :
    matrixExtension (R := R) (A := A) M ι n ∘ₗ cornerRestriction M r n = LinearMap.id :=
  LinearMap.ext (matrixExtension_cornerRestriction M r n)

variable {M} in
/-- **Matrix Morita invariance of Hochschild cohomology.** For a unital algebra `A` and a finite
nonempty index type `ι`, the generalized matrix trace induces a bijection on Hochschild cohomology
in every degree. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.bijective_iff_has_inverse.2
    ⟨cornerRestriction M r n, cornerRestriction_matrixExtension M r n,
      matrixExtension_cornerRestriction M r n⟩

/-- **Matrix Morita linear equivalence on Hochschild cohomology.** -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    hochschildCohomology R A M n ≃ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- Coercing `matrixExtensionEquiv` to a linear map recovers `matrixExtension`. -/
@[simp]
theorem coe_matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n :=
  (rfl)

/-- Applying `matrixExtensionEquiv` agrees with `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : hochschildCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- The inverse of `matrixExtensionEquiv` agrees with corner restriction at any matrix index
`r : ι`. -/
theorem matrixExtensionEquiv_symm_eq_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (r : ι) (n : ℕ) :
    ((matrixExtensionEquiv (R := R) (A := A) M ι n).symm :
      hochschildCohomology R (Matrix ι ι A) M n →ₗ[R] hochschildCohomology R A M n) =
      cornerRestriction M r n := by
  apply LinearMap.ext
  intro c
  apply (bijective_matrixExtension ι n).1
  rw [matrixExtension_cornerRestriction, ← matrixExtensionEquiv_apply]
  exact (matrixExtensionEquiv M ι n).apply_symm_apply c

end Unital

end hochschildCohomology

end TauCeti
