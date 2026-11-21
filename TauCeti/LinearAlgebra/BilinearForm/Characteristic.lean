/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.BilinearForm.Prod

/-!
# Characteristic vectors of symmetric bilinear forms

Let `B` be a symmetric bilinear form over a commutative ring `R`. A vector `w` is
*characteristic* for `B` when `B w x ≡ B x x` modulo `2` for every `x`.

Suppose that `c ^ 2 ≡ c` modulo `2` for every `c : R`, as for `ℤ` and `ℤ_[2]`. Then
`x ↦ B x x` is linear modulo `2`, so a perfect symmetric form on a free module has a
characteristic vector, and more generally every symmetric form on a finite free module has a
characteristic vector (even without perfection, by reducing modulo `(2)` to a Boolean ring and
splitting the finite set of Gram entries into idempotent pieces over `ℤ/2ℤ`). Any two
characteristic vectors of a perfect form differ by twice a vector, and therefore their
self-pairings agree modulo `8`. If `b` is an orthogonal basis, then `∑ i, b i` is
characteristic, and its self-pairing is the trace `∑ i, B (b i) (b i)` of the diagonal Gram matrix.
Consequently that trace modulo `8` is an isometry invariant of a perfect symmetric form with an
orthogonal basis. Over `ℤ_[2]` these are the odd unimodular forms, and the invariant is their
*oddity*, one of the entries of the Conway–Sloane `2`-adic symbol.

## Main definitions

* `LinearMap.BilinForm.IsCharacteristic`: `w` is characteristic for `B`.

## Main results

* `LinearMap.BilinForm.IsSymm.exists_isCharacteristic`: a perfect symmetric form on a free module
  has a characteristic vector.
* `LinearMap.BilinForm.IsSymm.exists_apply_eq_apply_self_zmod_two`: every symmetric form on a
  finite `ℤ/2ℤ`-module has a vector representing its diagonal `x ↦ B x x`.
* `LinearMap.BilinForm.IsSymm.exists_isCharacteristic_of_finite`: every symmetric form on a finite
  free module has a characteristic vector.
* `LinearMap.BilinForm.IsSymm.exists_apply_eq_apply_self`: every symmetric form on a finite free
  module over a ring with `c ^ 2 = c` has a vector representing its diagonal `x ↦ B x x`.
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

omit [CommRing R] [Module R M] in
/-- **Existence of a diagonal-representing vector over `ℤ/2ℤ`.** Every symmetric bilinear form on a
finite `ℤ/2ℤ`-module has a vector `w` satisfying `B w x = B x x` for every `x`. -/
theorem IsSymm.exists_apply_eq_apply_self_zmod_two [Module (ZMod 2) M] [Module.Finite (ZMod 2) M]
    {B : BilinForm (ZMod 2) M} (hB : B.IsSymm) :
    ∃ w : M, ∀ x : M, B w x = B x x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB_flip : LinearMap.flip B = B := by
    ext x y
    exact hB.eq y x
  have hc_sq : ∀ c : ZMod 2, c * c = c := fun | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
  let φ : M →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x ↦ B x x
      map_add' := fun x y ↦ by
        have htwo : B x y + B x y = 0 := by
          rw [← two_mul, ← Nat.cast_ofNat (R := ZMod 2), ZMod.natCast_self, zero_mul]
        simp only [map_add, LinearMap.add_apply, hB.eq y x]
        rw [add_assoc (B x x), ← add_assoc (B x y) (B x y), htwo, zero_add]
      map_smul' := fun c x ↦ by
        simp [smul_eq_mul, ← mul_assoc, hc_sq c] }
  have hmem : φ ∈ LinearMap.range B := by
    rw [← hB_flip, ← LinearMap.dualAnnihilator_ker_eq_range_flip (B := B),
      Submodule.mem_dualAnnihilator]
    intro u hu
    simp [φ, LinearMap.mem_ker.mp hu]
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, fun x ↦ LinearMap.congr_fun hw x⟩

/-- **Existence of characteristic vectors on finite free modules.** If `c ^ 2 ≡ c` modulo `2` for
every `c : R`, then every symmetric bilinear form on a finite free `R`-module has a characteristic
vector. -/
theorem IsSymm.exists_isCharacteristic_of_finite [Free R M] [Module.Finite R M] (hB : B.IsSymm)
    (h2 : ∀ c : R, (2 : R) ∣ c ^ 2 - c) : ∃ w, B.IsCharacteristic w := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, fun x ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  let b := Free.chooseBasis R M
  have : Finite (Free.ChooseBasisIndex R M) := Module.Finite.finite_basis b
  let _ : Fintype (Free.ChooseBasisIndex R M) := Fintype.ofFinite _
  -- Reduce modulo `(2)`: `S = R ⧸ (2)` satisfies `a * a = a` and `2 = 0`.
  let I : Ideal R := Ideal.span {(2 : R)}
  let S := R ⧸ I
  have h2_mem : (2 : R) ∈ I := Ideal.subset_span (Set.mem_singleton _)
  have h2S : ((2 : ℕ) : S) = 0 := by
    rw [Nat.cast_ofNat, ← map_ofNat (Ideal.Quotient.mk I) 2]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h2_mem
  have hmul_self (a : S) : a * a = a := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_mul, ← sub_eq_zero, ← map_sub]
    refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ?_)
    simpa [sq] using h2 r
  let toS : ZMod 2 →+* S := ZMod.castHom (ringChar.dvd h2S) S
  -- Partition `1 : S` into orthogonal idempotents over subsets `T` of the Gram entries `X`,
  -- reducing each piece to a symmetric system over `ℤ/2ℤ`.
  let G : Free.ChooseBasisIndex R M → Free.ChooseBasisIndex R M → S :=
    fun i j ↦ Ideal.Quotient.mk I (B (b i) (b j))
  let X : Finset S :=
    Finset.univ.image fun p : Free.ChooseBasisIndex R M × Free.ChooseBasisIndex R M ↦ G p.1 p.2
  have hG_mem (i j) : G i j ∈ X :=
    Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
  let e : Finset S → S := fun T ↦ (∏ x ∈ T, x) * ∏ x ∈ X \ T, (1 - x)
  have hsum_e : ∑ T ∈ X.powerset, e T = 1 := by
    have h := Finset.prod_add (fun x : S ↦ x) (fun x : S ↦ 1 - x) X
    simpa [e, add_sub_cancel] using h.symm
  have he_mul (T : Finset S) (x : S) (hx : x ∈ X) :
      e T * x = toS (if x ∈ T then 1 else 0) * e T := by
    by_cases hxT : x ∈ T
    · simp only [hxT, ↓reduceIte, map_one, one_mul]
      dsimp only [e]
      rw [← Finset.mul_prod_erase T (fun y ↦ y) hxT]
      calc
        x * (∏ y ∈ T.erase x, y) * (∏ y ∈ X \ T, (1 - y)) * x
            = (x * x) * (∏ y ∈ T.erase x, y) * (∏ y ∈ X \ T, (1 - y)) := by ring
        _ = x * (∏ y ∈ T.erase x, y) * (∏ y ∈ X \ T, (1 - y)) := by rw [hmul_self x]
    · simp only [hxT, ↓reduceIte, map_zero, zero_mul]
      have hx_sdiff : x ∈ X \ T := Finset.mem_sdiff.mpr ⟨hx, hxT⟩
      dsimp only [e]
      rw [← Finset.mul_prod_erase (X \ T) (fun y ↦ 1 - y) hx_sdiff]
      have h1x : (1 - x) * x = 0 := by rw [sub_mul, one_mul, hmul_self x, sub_self]
      calc
        (∏ y ∈ T, y) * ((1 - x) * ∏ y ∈ (X \ T).erase x, (1 - y)) * x
            = (∏ y ∈ T, y) * (∏ y ∈ (X \ T).erase x, (1 - y)) * ((1 - x) * x) := by ring
        _ = 0 := by rw [h1x, mul_zero]
  have hsol (T : Finset S) : ∃ c : Free.ChooseBasisIndex R M → ZMod 2,
      ∀ j, ∑ i, c i * (if G i j ∈ T then 1 else 0) = if G j j ∈ T then 1 else 0 := by
    let A : Matrix (Free.ChooseBasisIndex R M) (Free.ChooseBasisIndex R M) (ZMod 2) :=
      Matrix.of fun i j ↦ if G i j ∈ T then 1 else 0
    have hA : A.IsSymm := Matrix.ext fun i j ↦ by simp [A, G, hB.eq (b i) (b j)]
    obtain ⟨c, hc⟩ :=
      (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA).exists_apply_eq_apply_self_zmod_two
    refine ⟨c, fun j ↦ ?_⟩
    have hj := hc (Pi.single j 1)
    simp only [Matrix.toBilin'_apply', dotProduct, Matrix.mulVec, Pi.single_apply,
      mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte] at hj
    simpa only [A, Matrix.of_apply] using hj
  choose c hc using hsol
  -- Recombine the `ℤ/2ℤ` solutions via `e T` and lift the coefficients from `S` back to `R`.
  choose r hr using fun i ↦ Ideal.Quotient.mk_surjective (I := I)
    (∑ T ∈ X.powerset, toS (c T i) * e T)
  let w : M := ∑ i, r i • b i
  refine ⟨w, (hB.isCharacteristic_iff_forall_basis h2 b).2 fun j ↦ ?_⟩
  refine Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem (I := I)).mp ?_)
  rw [map_sub, sub_eq_zero]
  simp only [w, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    map_mul, hr]
  calc
    ∑ i, (∑ T ∈ X.powerset, toS (c T i) * e T) * G i j
        = ∑ T ∈ X.powerset, ∑ i, toS (c T i) * (e T * G i j) := by
          simp_rw [Finset.sum_mul, mul_assoc]
          exact Finset.sum_comm
    _ = ∑ T ∈ X.powerset, (∑ i, toS (c T i) * toS (if G i j ∈ T then 1 else 0)) * e T := by
          refine Finset.sum_congr rfl fun T _ ↦ ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [he_mul T (G i j) (hG_mem i j)]
          ring
    _ = ∑ T ∈ X.powerset, toS (if G j j ∈ T then 1 else 0) * e T := by
          refine Finset.sum_congr rfl fun T _ ↦ ?_
          rw [← hc T j, map_sum]
          simp_rw [map_mul]
    _ = ∑ T ∈ X.powerset, e T * G j j := by
          refine Finset.sum_congr rfl fun T _ ↦ ?_
          exact (he_mul T (G j j) (hG_mem j j)).symm
    _ = G j j := by
          rw [← Finset.sum_mul, hsum_e, one_mul]

/-- Every symmetric bilinear form on a finite free module over a ring in which every element
satisfies `c ^ 2 = c` has a vector `w` satisfying `B w x = B x x` for every `x`. -/
theorem IsSymm.exists_apply_eq_apply_self [Free R M] [Module.Finite R M] (hB : B.IsSymm)
    (hsq : ∀ c : R, c ^ 2 = c) : ∃ w : M, ∀ x : M, B w x = B x x := by
  have h2 : (2 : R) = 0 := by
    have h1 := hsq (-1)
    rw [neg_one_sq] at h1
    linear_combination h1
  obtain ⟨w, hw⟩ := hB.exists_isCharacteristic_of_finite fun c ↦ by simp [hsq c]
  exact ⟨w, fun x ↦ sub_eq_zero.mp (zero_dvd_iff.mp (h2 ▸ hw x))⟩

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
