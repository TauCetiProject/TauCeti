/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Characteristic vectors of symmetric bilinear forms

Let `B` be a symmetric bilinear form over a commutative ring `R`. A vector `w` is
*characteristic* for `B` when `B w x ≡ B x x` modulo `2` for every `x`.

Suppose that `c ^ 2 ≡ c` modulo `2` for every `c : R`, as for `ℤ` and `ℤ_[2]`. Then
`x ↦ B x x` is linear modulo `2`, so a perfect symmetric form on a free module has a
characteristic vector. Any two characteristic vectors differ by twice a vector, and therefore
their self-pairings agree modulo `8`. If `b` is an orthogonal basis, then `∑ i, b i` is
characteristic, and its self-pairing is the trace `∑ i, B (b i) (b i)` of the diagonal Gram matrix.
Consequently that trace modulo `8` is an isometry invariant of a perfect symmetric form with an
orthogonal basis. Over `ℤ_[2]` these are the odd unimodular forms, and the invariant is their
*oddity*, one of the entries of the Conway–Sloane `2`-adic symbol.

## Main definitions

* `LinearMap.BilinForm.IsCharacteristic`: `w` is characteristic for `B`.

## Main results

* `LinearMap.BilinForm.IsSymm.exists_isCharacteristic`: a perfect symmetric form on a free module
  has a characteristic vector.
* `LinearMap.BilinForm.IsCharacteristic.isCharacteristic_iff_exists_eq_add_two_smul`: the
  characteristic vectors form a single coset of twice the module.
* `LinearMap.BilinForm.IsCharacteristic.eight_dvd_apply_self_sub_apply_self`: characteristic
  vectors have the same self-pairing modulo `8`.
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
