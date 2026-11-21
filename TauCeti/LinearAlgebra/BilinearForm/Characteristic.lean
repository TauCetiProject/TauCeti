/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.BigOperators.Group.Finset.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.BilinearForm.Prod

/-!
# Characteristic vectors of symmetric bilinear forms

Let `B` be a symmetric bilinear form over a commutative ring `R`. A vector `w` is
*characteristic* for `B` when `B w x ≡ B x x` modulo `2` for every `x`.

Suppose that `c ^ 2 ≡ c` modulo `2` for every `c : R`, as for `ℤ` and `ℤ_[2]`. Then
`x ↦ B x x` is linear modulo `2`, so a symmetric form on a free module has a characteristic vector
whenever either the form is perfect (`LinearMap.BilinForm.IsSymm.exists_isCharacteristic`) or the
module is finite (`LinearMap.BilinForm.IsSymm.exists_isCharacteristic_of_finite`). For a perfect
form, any two characteristic vectors differ by twice a vector, and therefore their self-pairings
agree modulo `8`. If `b` is an orthogonal basis, then `∑ i, b i` is characteristic, and its
self-pairing is the trace `∑ i, B (b i) (b i)` of the diagonal Gram matrix. Consequently that trace
modulo `8` is an isometry invariant of a perfect symmetric form with an orthogonal basis. Over
`ℤ_[2]` these are the odd unimodular forms, and the invariant is their *oddity*, one of the entries
of the Conway–Sloane `2`-adic symbol.

## Main definitions

* `LinearMap.BilinForm.IsCharacteristic`: `w` is characteristic for `B`.

## Main results

* `LinearMap.BilinForm.IsSymm.exists_isCharacteristic`: a perfect symmetric form on a free module
  has a characteristic vector.
* `LinearMap.BilinForm.IsSymm.exists_isCharacteristic_of_finite`: any symmetric form on a finite
  free module has a characteristic vector, without assuming perfection.
* `LinearMap.BilinForm.Equivalent.forall_two_dvd_apply_self_iff`: isometric forms are even
  together.
* `LinearMap.BilinForm.IsCharacteristic.isCharacteristic_iff_exists_eq_add_two_smul`: the
  characteristic vectors form a single coset of twice the module.
* `LinearMap.BilinForm.IsCharacteristic.eight_dvd_apply_self_sub_apply_self`: characteristic
  vectors have the same self-pairing modulo `8`.
* `LinearMap.BilinForm.IsCharacteristic.eight_dvd_apply_self_of_forall_two_dvd`: for an even form
  these self-pairings are divisible by `8`.
* `LinearMap.BilinForm.Equivalent.eight_dvd_sum_apply_self_sub_sum_apply_self`: isometric perfect
  symmetric forms with orthogonal bases have diagonal Gram matrices with the same trace modulo `8`.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II and Appendix 4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] {B : BilinForm R M} {w w' : M}

/-- A vector `w` is *characteristic* for `B` when `B w x` is congruent to `B x x` modulo `2` for
every `x`. -/
def IsCharacteristic (B : BilinForm R M) (w : M) : Prop :=
  ∀ x, (2 : R) ∣ B w x - B x x

/-- The defining parity test for a characteristic vector. -/
theorem isCharacteristic_iff : B.IsCharacteristic w ↔ ∀ x, (2 : R) ∣ B w x - B x x :=
  Iff.rfl

/-- A vector is characteristic for a product form exactly when its components are characteristic. -/
@[simp]
theorem isCharacteristic_prod_iff {C : BilinForm R M'} {p : M × M'} :
    (B.prod C).IsCharacteristic p ↔ B.IsCharacteristic p.1 ∧ C.IsCharacteristic p.2 := by
  refine ⟨fun h ↦ ⟨fun x ↦ ?_, fun y ↦ ?_⟩, fun ⟨hB, hC⟩ x ↦ ?_⟩
  · simpa using h (x, 0)
  · simpa using h (0, y)
  · simpa only [prod_apply, add_sub_add_comm] using dvd_add (hB x.1) (hC x.2)

/-- The vector `1` is characteristic for multiplication when every scalar is idempotent modulo `2`.
-/
theorem isCharacteristic_mul_one (h : ∀ x : R, (2 : R) ∣ x ^ 2 - x) :
    IsCharacteristic (LinearMap.mul R R) 1 := by
  intro x
  simpa [LinearMap.mul_apply', sq] using (h x).neg_right

/-- A pair of characteristic vectors is characteristic for the product form. -/
theorem IsCharacteristic.prod {C : BilinForm R M'} {v : M'} (hw : B.IsCharacteristic w)
    (hv : C.IsCharacteristic v) : (B.prod C).IsCharacteristic (w, v) :=
  isCharacteristic_prod_iff.mpr ⟨hw, hv⟩

/-- Zero is characteristic exactly when every self-pairing is even. -/
@[simp]
theorem isCharacteristic_zero_iff : B.IsCharacteristic 0 ↔ ∀ x, (2 : R) ∣ B x x := by
  simp [isCharacteristic_iff]

/-- Adding twice a vector to a characteristic vector gives a characteristic vector. -/
theorem IsCharacteristic.add_two_smul (hw : B.IsCharacteristic w) (v : M) :
    B.IsCharacteristic (w + (2 : R) • v) := by
  intro x
  have h : B (w + (2 : R) • v) x - B x x = (B w x - B x x) + 2 * B v x := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [h]
  exact dvd_add (hw x) (dvd_mul_right _ _)

/-- Translation by twice a vector preserves and reflects the characteristic condition. -/
@[simp]
theorem isCharacteristic_add_two_smul_iff (v : M) :
    B.IsCharacteristic (w + (2 : R) • v) ↔ B.IsCharacteristic w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.add_two_smul v⟩
  simpa [smul_neg, add_assoc] using h.add_two_smul (-v)

/-- Negation preserves and reflects the characteristic condition. -/
@[simp]
theorem isCharacteristic_neg_iff : B.IsCharacteristic (-w) ↔ B.IsCharacteristic w := by
  have h : -w = w + (2 : R) • -w := by
    rw [two_smul]
    abel
  rw [h, isCharacteristic_add_two_smul_iff]

/-- The difference of two characteristic vectors pairs evenly with every vector. -/
theorem IsCharacteristic.two_dvd_apply_sub (hw : B.IsCharacteristic w)
    (hw' : B.IsCharacteristic w') (x : M) : (2 : R) ∣ B (w - w') x := by
  have h : B (w - w') x = (B w x - B x x) - (B w' x - B x x) := by
    rw [map_sub, LinearMap.sub_apply]
    ring
  rw [h]
  exact dvd_sub (hw x) (hw' x)

/-- An isometry identifies the characteristic vectors of the two forms. -/
@[simp]
theorem IsometryEquiv.isCharacteristic_apply_iff {C : BilinForm R M'} (f : B.IsometryEquiv C) :
    C.IsCharacteristic (f w) ↔ B.IsCharacteristic w := by
  refine ⟨fun h x ↦ by simpa using h (f x), fun h x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := EquivLike.surjective f x
  simpa using h y

/-- **Isometric forms are even together.** `0` is characteristic for `B` exactly when it is for
an isometric form, so `2` divides every `B x x` exactly when it divides every `C y y`. -/
theorem Equivalent.forall_two_dvd_apply_self_iff {C : BilinForm R M'} (h : B.Equivalent C) :
    (∀ x, (2 : R) ∣ B x x) ↔ ∀ y, (2 : R) ∣ C y y := by
  obtain ⟨f⟩ := h
  have := f.isCharacteristic_apply_iff (w := 0)
  rwa [map_zero, isCharacteristic_zero_iff, isCharacteristic_zero_iff, Iff.comm] at this

/-- **Characteristic vectors are tested on a basis.** If `c ^ 2 ≡ c` modulo `2` for every `c : R`,
then for a symmetric form it suffices to test the characteristic condition on the vectors of a
basis. -/
theorem IsSymm.isCharacteristic_iff_forall_basis (hB : B.IsSymm)
    (h2 : ∀ c : R, (2 : R) ∣ c ^ 2 - c) {ι : Type*} (b : Basis ι R M) :
    B.IsCharacteristic w ↔ ∀ i, (2 : R) ∣ B w (b i) - B (b i) (b i) := by
  refine ⟨fun hw i ↦ hw (b i), fun h x ↦ ?_⟩
  induction b.mem_span x using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact h i
  | zero => simp
  | add x y _ _ hx hy =>
    have hxy : B w (x + y) - B (x + y) (x + y) =
        (B w x - B x x) + (B w y - B y y) - 2 * B x y := by
      simp only [map_add, LinearMap.add_apply, hB.eq y x]
      ring
    rw [hxy]
    exact dvd_sub (dvd_add hx hy) (dvd_mul_right _ _)
  | smul c x _ hx =>
    have hcx : B w (c • x) - B (c • x) (c • x) = c * (B w x - B x x) - (c ^ 2 - c) * B x x := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hcx]
    exact dvd_sub (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_left (h2 c) _)

/-- **Existence of characteristic vectors.** If `c ^ 2 ≡ c` modulo `2` for every `c : R`, then a
perfect symmetric form on a free module has a characteristic vector. -/
theorem IsSymm.exists_isCharacteristic [Free R M] [B.IsPerfPair] (hB : B.IsSymm)
    (h2 : ∀ c : R, (2 : R) ∣ c ^ 2 - c) : ∃ w, B.IsCharacteristic w := by
  let b := Free.chooseBasis R M
  let φ : Dual R M := b.constr R fun i ↦ B (b i) (b i)
  refine ⟨B.toPerfPair.symm φ, (hB.isCharacteristic_iff_forall_basis h2 b).2 fun i ↦ ?_⟩
  simp [φ]

/-- Over a Boolean ring (`x * x = x`), every finite symmetric system `∑ i, u i * a i j = a j j`
has a solution. Proved by strong induction on the dimension, gluing solutions across the
idempotent partition generated by the last row and column. -/
private theorem exists_sum_mul_eq_diag_of_sq_eq_self {S : Type*} [CommRing S]
    (hsq : ∀ x : S, x * x = x) :
    ∀ (n : ℕ) (a : Fin n → Fin n → S), (∀ i j, a i j = a j i) →
      ∃ u : Fin n → S, ∀ j, ∑ i, u i * a i j = a j j := by
  have hadd (x : S) : x + x = 0 := by linear_combination hsq (x + x) - 4 * hsq x
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro a ha
    match n with
    | 0 => exact ⟨Fin.elim0, fun j ↦ j.elim0⟩
    | 1 => exact ⟨fun _ ↦ 1, fun j ↦ by rw [Fin.eq_zero j]; simp⟩
    | m + 2 =>
      let P (e : S) : Prop := ∃ u : Fin (m + 2) → S, ∀ j, e * ∑ i, u i * a i j = e * a j j
      have hmul {a' e : S} (ha' : P a') : P (a' * e) :=
        let ⟨u, hu⟩ := ha'
        ⟨u, fun j ↦ by rw [mul_right_comm, hu, mul_right_comm]⟩
      have hjoin {c e : S} (h₁ : P (c * e)) (h₀ : P (c * (1 - e))) : P c := by
        obtain ⟨u₁, hu₁⟩ := h₁
        obtain ⟨u₂, hu₂⟩ := h₀
        refine ⟨fun i ↦ e * u₁ i + (1 - e) * u₂ i, fun j ↦ ?_⟩
        calc c * ∑ i, (e * u₁ i + (1 - e) * u₂ i) * a i j
            = c * e * ∑ i, u₁ i * a i j + c * (1 - e) * ∑ i, u₂ i * a i j := by
              simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
              ring
          _ = c * e * a j j + c * (1 - e) * a j j := by rw [hu₁, hu₂]
          _ = c * a j j := by ring
      let last : Fin (m + 2) := Fin.last (m + 1)
      let d : S := a last last
      -- Case `d = 1`: eliminate the last coordinate using the pivot `d`.
      have hPd : P d := by
        let a' (i j : Fin (m + 1)) : S :=
          a i.castSucc j.castSucc + a i.castSucc last * a last j.castSucc
        have ha' (i j : Fin (m + 1)) : a' i j = a' j i := by
          simp only [a', ha i.castSucc j.castSucc, ha i.castSucc last, ha last j.castSucc]
          ring
        obtain ⟨u', hu'⟩ := ih (m + 1) (by omega) a' ha'
        let s : S := ∑ i : Fin (m + 1), u' i * a i.castSucc last
        refine ⟨Fin.snoc u' (1 + s), fun j ↦ ?_⟩
        refine Fin.lastCases ?_ (fun j ↦ ?_) j
        · rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          dsimp only [d, s]
          linear_combination s * hsq (a last last) + s * hadd (a last last)
        · rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          have hsum : (∑ i : Fin (m + 1), u' i * a i.castSucc j.castSucc) +
              (1 + s) * a last j.castSucc =
              (∑ i : Fin (m + 1), u' i * a' i j) + a last j.castSucc := by
            simp only [a', s, mul_add, add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
            ring
          rw [hsum, hu' j]
          dsimp only [a']
          rw [ha j.castSucc last]
          congr 1
          linear_combination hsq (a last j.castSucc) + hadd (a last j.castSucc)
      -- Case `d = 0`, `a k last = 1`: eliminate the hyperbolic pair `{k, last}`.
      have hPk (k : Fin (m + 1)) : P ((1 - d) * a k.castSucc last) := by
        let e : S := a k.castSucc last
        let c : S := (1 - d) * e
        have hcd : c * d = 0 := by linear_combination -e * hsq d
        have hce : c * e = c := by linear_combination (1 - d) * hsq e
        let f (i : Fin m) : Fin (m + 2) := (k.succAbove i).castSucc
        let a'' (i j : Fin m) : S :=
          a (f i) (f j) + a (f i) last * a k.castSucc (f j) +
            a (f i) k.castSucc * a last (f j) +
            a k.castSucc k.castSucc * a (f i) last * a last (f j)
        have ha'' (i j : Fin m) : a'' i j = a'' j i := by
          simp only [a'', ha (f i) (f j), ha (f i) last, ha k.castSucc (f j),
            ha (f i) k.castSucc, ha last (f j)]
          ring
        obtain ⟨u'', hu''⟩ := ih m (by omega) a'' ha''
        let vk : S := ∑ i : Fin m, u'' i * a (f i) last
        let v : Fin (m + 1) → S := k.insertNth vk u''
        let sk : S := ∑ i : Fin (m + 1), v i * a i.castSucc k.castSucc
        let u : Fin (m + 2) → S := Fin.snoc v (a k.castSucc k.castSucc + sk)
        have hsum_u (j : Fin (m + 2)) :
            ∑ i, u i * a i j = vk * a k.castSucc j + (∑ i : Fin m, u'' i * a (f i) j) +
              (a k.castSucc k.castSucc + sk) * a last j := by
          rw [Fin.sum_univ_castSucc, Fin.sum_univ_succAbove _ k]
          simp only [u, v, f, last, Fin.snoc_castSucc, Fin.snoc_last, Fin.insertNth_apply_same,
            Fin.insertNth_apply_succAbove]
        refine ⟨u, fun j ↦ ?_⟩
        refine Fin.lastCases ?_ (fun j ↦ ?_) j
        · rw [hsum_u last]
          dsimp only [c, d, e, vk, sk] at hcd hce ⊢
          linear_combination
            vk * hce + (a k.castSucc k.castSucc + sk) * hcd + hadd (c * vk) - hcd
        · refine Fin.succAboveCases k ?_ (fun j' ↦ ?_) j
          · rw [Fin.sum_univ_castSucc]
            simp only [u, Fin.snoc_castSucc, Fin.snoc_last]
            rw [ha last k.castSucc]
            dsimp only [c, e, sk] at hce ⊢
            linear_combination (a k.castSucc k.castSucc + sk) * hce + hadd (c * sk)
          · congr 1
            rw [hsum_u]
            have hsk : sk = vk * a k.castSucc k.castSucc +
                ∑ i : Fin m, u'' i * a (f i) k.castSucc := by
              dsimp only [sk]
              rw [Fin.sum_univ_succAbove _ k]
              simp only [v, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
              rfl
            have hterms : ∀ i : Fin m, u'' i * a'' i j' =
                u'' i * a (f i) (f j') +
                  u'' i * a (f i) last * a k.castSucc (f j') +
                  u'' i * a (f i) last * a k.castSucc k.castSucc * a last (f j') +
                  u'' i * a (f i) k.castSucc * a last (f j') := fun i ↦ by
              dsimp only [a'']; ring
            have hsum : vk * a k.castSucc (f j') + (∑ i : Fin m, u'' i * a (f i) (f j')) +
                (a k.castSucc k.castSucc + sk) * a last (f j') =
                (∑ i : Fin m, u'' i * a'' i j') + a k.castSucc k.castSucc * a last (f j') := by
              rw [hsk]
              simp only [hterms, vk, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
              ring
            dsimp only [f] at hsum
            rw [hsum, hu'' j']
            dsimp only [a'', f]
            rw [ha (k.succAbove j').castSucc last, ha k.castSucc (k.succAbove j').castSucc]
            linear_combination
              hadd (a last (k.succAbove j').castSucc * a (k.succAbove j').castSucc k.castSucc) +
              a k.castSucc k.castSucc *
                (hsq (a last (k.succAbove j').castSucc) + hadd (a last (k.succAbove j').castSucc))
      -- Case `d = 0` and `a k last = 0` for all `k`: the last row/column vanishes, so pad with `0`.
      have hPrest : P ((1 - d) * ∏ k : Fin (m + 1), (1 - a k.castSucc last)) := by
        let a₀ (i j : Fin (m + 1)) : S := a i.castSucc j.castSucc
        obtain ⟨u₀, hu₀⟩ := ih (m + 1) (by omega) a₀ fun i j ↦ ha i.castSucc j.castSucc
        let r : S := (1 - d) * ∏ k : Fin (m + 1), (1 - a k.castSucc last)
        have hrd : r * d = 0 := by
          dsimp only [r]
          linear_combination -(∏ k : Fin (m + 1), (1 - a k.castSucc last)) * hsq d
        have hrk (k : Fin (m + 1)) : r * a k.castSucc last = 0 := by
          dsimp only [r]
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
          linear_combination
            -((1 - d) * ∏ t ∈ Finset.univ.erase k, (1 - a t.castSucc last)) *
              hsq (a k.castSucc last)
        refine ⟨Fin.snoc u₀ 0, fun j ↦ ?_⟩
        refine Fin.lastCases ?_ (fun j ↦ ?_) j
        · rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero, Finset.mul_sum]
          dsimp only [r, d] at hrd hrk ⊢
          rw [hrd]
          exact Finset.sum_eq_zero fun i _ ↦ by
            rw [← mul_assoc, mul_comm ((1 - a last last) * _), mul_assoc, hrk, mul_zero]
        · rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
          exact congrArg (r * ·) (hu₀ j)
      have hP1 : P 1 := by
        refine hjoin (e := d) (by rwa [one_mul]) ?_
        rw [one_mul]
        exact TauCeti.of_mul_prod_of_forall_mul (fun _ ↦ hmul) (fun _ ↦ hjoin) hPrest
          fun k _ ↦ hPk k
      obtain ⟨u, hu⟩ := hP1
      exact ⟨u, fun j ↦ by simpa using hu j⟩

/-- **Existence of characteristic vectors on finite free modules.** If `c ^ 2 ≡ c` modulo `2` for
every `c : R`, then every symmetric bilinear form on a finite free `R`-module has a characteristic
vector, without assuming perfection. -/
theorem IsSymm.exists_isCharacteristic_of_finite [Free R M] [Module.Finite R M]
    (hB : B.IsSymm) (h2 : ∀ c : R, (2 : R) ∣ c ^ 2 - c) : ∃ w, B.IsCharacteristic w := by
  let _ := Module.Free.ChooseBasisIndex.fintype R M
  let b := (Free.chooseBasis R M).reindex (Fintype.equivFin (Free.ChooseBasisIndex R M))
  let I : Ideal R := Ideal.span {(2 : R)}
  have hsq (x : R ⧸ I) : x * x = x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    simpa [sq] using h2 r
  obtain ⟨u, hu⟩ := exists_sum_mul_eq_diag_of_sq_eq_self hsq _
    (fun i j ↦ Ideal.Quotient.mk I (B (b i) (b j)))
    (fun i j ↦ congrArg (Ideal.Quotient.mk I) (hB.eq (b i) (b j)))
  choose c hc using fun i ↦ Ideal.Quotient.mk_surjective (u i)
  let w : M := ∑ i, c i • b i
  refine ⟨w, (hB.isCharacteristic_iff_forall_basis h2 b).2 fun j ↦ ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  simpa only [I, w, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    map_mul, hc] using hu j

/-- **Two characteristic vectors differ by twice a vector** when the form is perfect and the
module is free. -/
theorem IsCharacteristic.exists_eq_add_two_smul [Free R M] [B.IsPerfPair]
    (hw : B.IsCharacteristic w) (hw' : B.IsCharacteristic w') : ∃ v, w' = w + (2 : R) • v := by
  let b := Free.chooseBasis R M
  choose c hc using fun i ↦ hw'.two_dvd_apply_sub hw (b i)
  refine ⟨B.toPerfPair.symm (b.constr R c), ?_⟩
  rw [← sub_eq_iff_eq_add']
  apply B.toPerfPair.injective
  refine b.ext fun i ↦ ?_
  simpa using hc i

/-- **The characteristic vectors form a coset of twice the module.** For a perfect form on a free
module, once `w` is characteristic, the characteristic vectors are exactly the vectors
`w + 2 • v`. -/
theorem IsCharacteristic.isCharacteristic_iff_exists_eq_add_two_smul [Free R M] [B.IsPerfPair]
    (hw : B.IsCharacteristic w) : B.IsCharacteristic w' ↔ ∃ v, w' = w + (2 : R) • v := by
  refine ⟨hw.exists_eq_add_two_smul, ?_⟩
  rintro ⟨v, rfl⟩
  exact hw.add_two_smul v

/-- Translating a characteristic vector by twice a vector changes its self-pairing by a multiple
of `8`. -/
theorem IsSymm.eight_dvd_apply_add_two_smul_sub (hB : B.IsSymm) (hw : B.IsCharacteristic w)
    (v : M) : (8 : R) ∣ B (w + (2 : R) • v) (w + (2 : R) • v) - B w w := by
  obtain ⟨k, hk⟩ := hw v
  refine ⟨k + B v v, ?_⟩
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hB.eq v w]
  linear_combination 4 * hk

/-- **The self-pairing of a characteristic vector is well defined modulo `8`.** For a perfect
symmetric form on a free module, any two characteristic vectors have self-pairings congruent
modulo `8`. -/
theorem IsCharacteristic.eight_dvd_apply_self_sub_apply_self [Free R M] [B.IsPerfPair]
    (hB : B.IsSymm) (hw : B.IsCharacteristic w) (hw' : B.IsCharacteristic w') :
    (8 : R) ∣ B w' w' - B w w := by
  obtain ⟨v, rfl⟩ := hw.exists_eq_add_two_smul hw'
  exact hB.eight_dvd_apply_add_two_smul_sub hw v

/-- **Even forms have characteristic norms divisible by `8`.** If `2` divides every `B x x`, then
`0` is characteristic, so for a perfect form on a free module every characteristic vector has
self-pairing divisible by `8`. -/
theorem IsCharacteristic.eight_dvd_apply_self_of_forall_two_dvd [Free R M] [B.IsPerfPair]
    (hw : B.IsCharacteristic w) (heven : ∀ x, (2 : R) ∣ B x x) :
    (8 : R) ∣ B w w := by
  obtain ⟨v, rfl⟩ := (isCharacteristic_zero_iff.mpr heven).exists_eq_add_two_smul hw
  obtain ⟨k, hk⟩ := heven v
  exact ⟨k, by simp only [zero_add, map_smul, LinearMap.smul_apply, smul_eq_mul, hk]; ring⟩

section Orthogonal

variable {ι : Type*} [Fintype ι]

/-- **The sum of an orthogonal basis is characteristic** when `c ^ 2 ≡ c` modulo `2` for every
`c : R`. -/
theorem iIsOrtho.isCharacteristic_sum (h2 : ∀ c : R, (2 : R) ∣ c ^ 2 - c)
    {b : Basis ι R M} (hb : B.iIsOrtho b) : B.IsCharacteristic (∑ i, b i) := by
  classical
  refine (hb.isSymm.isCharacteristic_iff_forall_basis h2 b).2 fun i ↦ ?_
  rw [map_sum, LinearMap.sum_apply,
    Finset.sum_eq_single i (fun j _ hji ↦ (iIsOrtho_def.mp hb) j i hji) (by simp), sub_self]
  exact dvd_zero _

/-- **The trace of a diagonal Gram matrix modulo `8` is an isometry invariant.** Let `c ^ 2 ≡ c`
modulo `2` for every `c : R`, as over `ℤ` and `ℤ_[2]`. If a perfect form `B` is isometric to
`C`, and `b` and `c` are orthogonal bases for `B` and `C`, then the traces
`∑ i, B (b i) (b i)` and `∑ j, C (c j) (c j)` agree modulo `8`. Over `ℤ_[2]` this is the invariance
of the oddity of an odd unimodular form. -/
theorem Equivalent.eight_dvd_sum_apply_self_sub_sum_apply_self {C : BilinForm R M'}
    (h : B.Equivalent C) [B.IsPerfPair] (h2 : ∀ c : R, (2 : R) ∣ c ^ 2 - c)
    {κ : Type*} [Fintype κ] {b : Basis ι R M} {c : Basis κ R M'} (hb : B.iIsOrtho b)
    (hc : C.iIsOrtho c) :
    (8 : R) ∣ ∑ j, C (c j) (c j) - ∑ i, B (b i) (b i) := by
  obtain ⟨f⟩ := h
  have : Free R M := .of_basis b
  let c' := c.map (f.symm : M' ≃ₗ[R] M)
  have hc'apply : ∀ j k, B (c' j) (c' k) = C (c j) (c k) := fun j k ↦ by
    simp [c']
  have hc' : B.iIsOrtho c' := iIsOrtho_def.mpr fun j k hjk ↦ by
    rw [hc'apply]
    exact iIsOrtho_def.mp hc j k hjk
  have key := (hb.isCharacteristic_sum h2).eight_dvd_apply_self_sub_apply_self hb.isSymm
    (hc'.isCharacteristic_sum h2)
  rwa [hb.apply_sum_sum, hc'.apply_sum_sum, Finset.sum_congr rfl fun j _ ↦ hc'apply j j] at key

end Orthogonal

end LinearMap.BilinForm
