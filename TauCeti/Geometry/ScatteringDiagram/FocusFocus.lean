/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraTower
public import TauCeti.Geometry.ScatteringDiagram.SlabAlgebra.Basic

/-!
# The focus-focus model algebra and theta multiplication

In the two-dimensional focus-focus toric degeneration with a single shear wall `1 + w` along a ray,
the local coordinate ring modulo `t ^ (k + 1)` across the wall is modeled over a commutative ring
`K` by `ModelAlgebra K k := K[t, w, w⁻¹, x, y] ⧸ (w w⁻¹ - 1, t ^ (k + 1), x y - t (1 + w))`.

In this model, the tangential coordinate `w` is invertible (`modelW`) and the broken-line theta
elements `modelTheta K k n b` (`ϑ_{n, b}`) take the explicit form `x ^ |n| * w ^ b` for `n < 0`,
`w ^ b` for `n = 0`, and `y ^ n * w ^ b` for `n > 0`. Identifying `ModelAlgebra K k` canonically
with the slab algebra over `S_k[w, w⁻¹]` (`S_k = K[t] ⧸ (t ^ (k + 1))`) with wall factor
`q = t (1 + w)` yields:

1. **Theta multiplication (`FocusFocus.modelTheta_mul`)**: for all `n, m, b, c : ℤ` and
   `r = (|n| + |m| - |n + m|) / 2`,
   `ϑ_{n, b} * ϑ_{m, c} = t ^ r * ∑ j ∈ Finset.range (r + 1), binom(r, j) * ϑ_{n + m, b + c + j}`,
   derived directly from `SlabAlgebra.Z_mul_Z` and the binomial expansion of `(1 + w) ^ r`.
2. **Slab-algebra isomorphism and `K`-basis (`FocusFocus.modelSlabEquiv`,
   `FocusFocus.modelBasis`)**: `ModelAlgebra K k` is canonically `K`-algebra isomorphic to
   `SlabAlgebra (LaurentPolynomial (AdjoinRoot (X ^ (k + 1)))) (t (1 + w))`, and the monomials
   `t ^ i * ϑ_{n, b}` (`i : Fin (k + 1)`, `n, b : ℤ`) form a `K`-basis of `ModelAlgebra K k`.
3. **Nontriviality of opposing-ray multiplication**: for `1 ≤ k` over any nontrivial ring `K`
   (in particular `K = ℤ`, `k = 2`), `ϑ_{-1, b} * ϑ_{1, c} = t * (ϑ_{0, b + c} + ϑ_{0, b + c + 1})`
   is nonzero.

## Main definitions

* `TauCeti.FocusFocus.Coordinate`, `TauCeti.FocusFocus.Ambient`, `TauCeti.FocusFocus.modelIdeal`,
  `TauCeti.FocusFocus.ModelAlgebra`: the focus-focus quotient algebra at order `k`.
* `TauCeti.FocusFocus.coordinate`, `TauCeti.FocusFocus.modelW`, `TauCeti.FocusFocus.modelTheta`:
  coordinate classes, the tangential unit `w`, and the theta elements `ϑ_{n, b}`.
* `TauCeti.FocusFocus.BaseRing`, `TauCeti.FocusFocus.modelWallFactor`,
  `TauCeti.FocusFocus.modelSlabEquiv`: canonical `K`-algebra equivalence with
  `SlabAlgebra (LaurentPolynomial (BaseRing K k)) (modelWallFactor K k)`.
* `TauCeti.FocusFocus.modelBasis`: the `K`-basis `(i, n, b) ↦ t ^ i * ϑ_{n, b}` of
  `ModelAlgebra K k`.

## Main results

* `TauCeti.FocusFocus.modelTheta_mul`: explicit structure-constant multiplication law for
  `modelTheta`.
* `TauCeti.FocusFocus.pow_t_mul_modelTheta_ne_zero`, `TauCeti.FocusFocus.modelTheta_ne_zero`:
  nonvanishing of `t ^ r * ϑ_{n, b}` for `r ≤ k` over a nontrivial ring `K`.
* `TauCeti.FocusFocus.modelTheta_neg_one_mul_one`,
  `TauCeti.FocusFocus.modelTheta_neg_one_mul_one_ne_zero`: worked opposing-ray product
  `ϑ_{-1, b} * ϑ_{1, c} = t * (ϑ_{0, b + c} + ϑ_{0, b + c + 1}) ≠ 0` for `1 ≤ k`.

## References

* [M. Gross and B. Siebert, *An Invitation to Toric Degenerations*][GrossSiebert2011], §2.3
  (arXiv:0808.2749).
* [M. Gross, P. Hacking, and B. Siebert, *Theta functions on varieties with effective
  anti-canonical class*][GrossHackingSiebert2022], §3 (arXiv:1601.07081).
-/

public noncomputable section

namespace TauCeti.FocusFocus

/-- Coordinates for `K[t, w, w⁻¹, x, y]`, with the inverse relation imposed in the quotient. -/
inductive Coordinate where
  | t | w | wInv | x | y
  deriving DecidableEq

open Coordinate

section Model

variable (K : Type*) [CommRing K]

/-- The polynomial ring `K[t, w, w⁻¹, x, y]` before the focus-focus relations. -/
abbrev Ambient := MvPolynomial Coordinate K

/-- The focus-focus ideal `(w w⁻¹ - 1, t ^ (k + 1), x y - t (1 + w))` at order `k`. -/
def modelIdeal (k : ℕ) : Ideal (Ambient K) :=
  Ideal.span {MvPolynomial.X w * MvPolynomial.X wInv - 1, MvPolynomial.X t ^ (k + 1),
    MvPolynomial.X x * MvPolynomial.X y - MvPolynomial.X t * (1 + MvPolynomial.X w)}

/-- The focus-focus model algebra `K[t, w^{±1}, x, y] ⧸ (t ^ (k + 1), x y - t (1 + w))` at
order `k`. -/
abbrev ModelAlgebra (k : ℕ) := Ambient K ⧸ modelIdeal K k

/-- A coordinate class in a quotient of `Ambient K`. -/
def coordinate (I : Ideal (Ambient K)) (c : Coordinate) : Ambient K ⧸ I :=
  Ideal.Quotient.mk I (MvPolynomial.X c)

/-- `w` as a unit of `ModelAlgebra K k`, with inverse `w⁻¹`. -/
def modelW (k : ℕ) : (ModelAlgebra K k)ˣ :=
  have hw : coordinate K (modelIdeal K k) w * coordinate K (modelIdeal K k) wInv = 1 := by
    rw [coordinate, coordinate, ← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.subset_span (Set.mem_insert _ _)
  ⟨coordinate K (modelIdeal K k) w, coordinate K (modelIdeal K k) wInv, hw,
    (mul_comm (coordinate K (modelIdeal K k) wInv) (coordinate K (modelIdeal K k) w)).trans hw⟩

@[simp] theorem modelW_val (k : ℕ) : ↑(modelW K k) = coordinate K (modelIdeal K k) w := (rfl)

@[simp] theorem modelW_inv (k : ℕ) : ↑(modelW K k)⁻¹ = coordinate K (modelIdeal K k) wInv := (rfl)

@[simp] theorem coordinate_w_mul_wInv (k : ℕ) :
    coordinate K (modelIdeal K k) w * coordinate K (modelIdeal K k) wInv = 1 :=
  (modelW K k).val_inv

@[simp] theorem coordinate_wInv_mul_w (k : ℕ) :
    coordinate K (modelIdeal K k) wInv * coordinate K (modelIdeal K k) w = 1 :=
  (modelW K k).inv_val

/-- The truncation relation `t ^ (k + 1) = 0` in `ModelAlgebra K k`. -/
@[simp] theorem coordinate_t_pow_succ (k : ℕ) :
    coordinate K (modelIdeal K k) t ^ (k + 1) = 0 := by
  rw [coordinate, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

/-- Higher powers `t ^ r` vanish in `ModelAlgebra K k` whenever `k < r`. -/
theorem coordinate_t_pow_eq_zero_of_lt (k : ℕ) {r : ℕ} (hr : k < r) :
    coordinate K (modelIdeal K k) t ^ r = 0 := by
  rw [← Nat.add_sub_cancel' hr, pow_add, coordinate_t_pow_succ, zero_mul]

/-- The slab relation `x * y = t * (1 + w)` in `ModelAlgebra K k`. -/
@[simp] theorem coordinate_x_mul_y (k : ℕ) :
    coordinate K (modelIdeal K k) x * coordinate K (modelIdeal K k) y =
      coordinate K (modelIdeal K k) t * (1 + coordinate K (modelIdeal K k) w) := by
  rw [coordinate, coordinate, coordinate, coordinate, ← map_mul,
    ← map_one (Ideal.Quotient.mk _), ← map_add, ← map_mul, Ideal.Quotient.eq]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- The model theta element `ϑ_{n, b}`: `x ^ |n| * w ^ b` for `n < 0`, `w ^ b` for `n = 0`, and
`y ^ n * w ^ b` for `n > 0`. -/
def modelTheta (k : ℕ) (n b : ℤ) : ModelAlgebra K k :=
  (if n < 0 then coordinate K (modelIdeal K k) x ^ n.natAbs
    else coordinate K (modelIdeal K k) y ^ n.natAbs) * ↑(modelW K k ^ b)

@[simp] theorem modelTheta_zero (k : ℕ) (b : ℤ) : modelTheta K k 0 b = ↑(modelW K k ^ b) := by
  simp [modelTheta]

theorem modelTheta_of_neg (k : ℕ) {n : ℤ} (hn : n < 0) (b : ℤ) :
    modelTheta K k n b = coordinate K (modelIdeal K k) x ^ n.natAbs * ↑(modelW K k ^ b) := by
  simp [modelTheta, hn]

theorem modelTheta_of_nonneg (k : ℕ) {n : ℤ} (hn : 0 ≤ n) (b : ℤ) :
    modelTheta K k n b = coordinate K (modelIdeal K k) y ^ n.natAbs * ↑(modelW K k ^ b) := by
  simp [modelTheta, not_lt.mpr hn]

end Model

/-! ### Universal property, truncation, and scalar extension -/

section Universal

private def coordVal {A : Type*} (vt vw vwInv vx vy : A) : Coordinate → A
  | .t => vt | .w => vw | .wInv => vwInv | .x => vx | .y => vy

/-- Ring homomorphisms out of `ModelAlgebra K k` are determined by `K` and the five coordinates. -/
theorem ringHom_ext {K A : Type*} [CommRing K] [NonAssocSemiring A] {k : ℕ}
    {f g : ModelAlgebra K k →+* A}
    (hK : ∀ r : K, f (algebraMap K (ModelAlgebra K k) r) = g (algebraMap K (ModelAlgebra K k) r))
    (hc : ∀ c, f (coordinate K (modelIdeal K k) c) = g (coordinate K (modelIdeal K k) c)) :
    f = g := by
  apply Ideal.Quotient.ringHom_ext; ext p
  induction p using MvPolynomial.induction_on with
  | C r => exact hK r
  | add p₁ p₂ hp₁ hp₂ => simp only [RingHom.comp_apply, map_add] at hp₁ hp₂ ⊢; rw [hp₁, hp₂]
  | mul_X p₁ c hp₁ => simp only [RingHom.comp_apply, map_mul] at hp₁ ⊢; rw [hp₁, ← coordinate, hc c]

/-- `K`-algebra homomorphisms out of `ModelAlgebra K k` are determined by the five coordinates. -/
@[ext] theorem algHom_ext {K A : Type*} [CommRing K] [Semiring A] [Algebra K A] {k : ℕ}
    {f g : ModelAlgebra K k →ₐ[K] A}
    (hc : ∀ c, f (coordinate K (modelIdeal K k) c) = g (coordinate K (modelIdeal K k) c)) :
    f = g :=
  AlgHom.toRingHom_injective (ringHom_ext (fun r => (f.commutes r).trans (g.commutes r).symm) hc)

section LiftRingHom

variable {K A : Type*} [CommRing K] [CommRing A] {k : ℕ} (f : K →+* A)
  (vt vw vwInv vx vy : A) (hw : vw * vwInv = 1) (ht : vt ^ (k + 1) = 0)
  (hxy : vx * vy = vt * (1 + vw))

/-- Universal property of `ModelAlgebra K k` for ring homomorphisms. -/
def liftRingHom : ModelAlgebra K k →+* A :=
  Ideal.Quotient.lift (modelIdeal K k)
    (MvPolynomial.eval₂Hom f (coordVal vt vw vwInv vx vy)) fun _ hp => by
      refine RingHom.mem_ker.mp (Ideal.span_le.mpr ?_ hp)
      rintro q (rfl | rfl | rfl) <;> simp [RingHom.mem_ker, coordVal, hw, ht, hxy]

@[simp] theorem liftRingHom_algebraMap (r : K) :
    liftRingHom f vt vw vwInv vx vy hw ht hxy (algebraMap K (ModelAlgebra K k) r) = f r := by
  rw [IsScalarTower.algebraMap_apply K (Ambient K) (ModelAlgebra K k) r,
    MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq, liftRingHom,
    Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]

@[simp] theorem liftRingHom_coordinate_t :
    liftRingHom f vt vw vwInv vx vy hw ht hxy (coordinate K (modelIdeal K k) t) = vt := by
  rw [liftRingHom, coordinate, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X', coordVal]

@[simp] theorem liftRingHom_coordinate_w :
    liftRingHom f vt vw vwInv vx vy hw ht hxy (coordinate K (modelIdeal K k) w) = vw := by
  rw [liftRingHom, coordinate, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X', coordVal]

@[simp] theorem liftRingHom_coordinate_wInv :
    liftRingHom f vt vw vwInv vx vy hw ht hxy (coordinate K (modelIdeal K k) wInv) = vwInv := by
  rw [liftRingHom, coordinate, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X', coordVal]

@[simp] theorem liftRingHom_coordinate_x :
    liftRingHom f vt vw vwInv vx vy hw ht hxy (coordinate K (modelIdeal K k) x) = vx := by
  rw [liftRingHom, coordinate, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X', coordVal]

@[simp] theorem liftRingHom_coordinate_y :
    liftRingHom f vt vw vwInv vx vy hw ht hxy (coordinate K (modelIdeal K k) y) = vy := by
  rw [liftRingHom, coordinate, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X', coordVal]

end LiftRingHom

section LiftAlgHom

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {k : ℕ}
  (vt vw vwInv vx vy : A) (hw : vw * vwInv = 1) (ht : vt ^ (k + 1) = 0)
  (hxy : vx * vy = vt * (1 + vw))

/-- Universal property of `ModelAlgebra K k` for `K`-algebra homomorphisms. -/
def liftAlgHom : ModelAlgebra K k →ₐ[K] A :=
  AlgHom.mk (liftRingHom (algebraMap K A) vt vw vwInv vx vy hw ht hxy)
    (liftRingHom_algebraMap (algebraMap K A) vt vw vwInv vx vy hw ht hxy)

@[simp] theorem liftAlgHom_coordinate_t :
    liftAlgHom vt vw vwInv vx vy hw ht hxy (coordinate K (modelIdeal K k) t) = vt :=
  liftRingHom_coordinate_t (algebraMap K A) vt vw vwInv vx vy hw ht hxy

@[simp] theorem liftAlgHom_coordinate_w :
    liftAlgHom vt vw vwInv vx vy hw ht hxy (coordinate K (modelIdeal K k) w) = vw :=
  liftRingHom_coordinate_w (algebraMap K A) vt vw vwInv vx vy hw ht hxy

@[simp] theorem liftAlgHom_coordinate_wInv :
    liftAlgHom vt vw vwInv vx vy hw ht hxy (coordinate K (modelIdeal K k) wInv) = vwInv :=
  liftRingHom_coordinate_wInv (algebraMap K A) vt vw vwInv vx vy hw ht hxy

@[simp] theorem liftAlgHom_coordinate_x :
    liftAlgHom vt vw vwInv vx vy hw ht hxy (coordinate K (modelIdeal K k) x) = vx :=
  liftRingHom_coordinate_x (algebraMap K A) vt vw vwInv vx vy hw ht hxy

@[simp] theorem liftAlgHom_coordinate_y :
    liftAlgHom vt vw vwInv vx vy hw ht hxy (coordinate K (modelIdeal K k) y) = vy :=
  liftRingHom_coordinate_y (algebraMap K A) vt vw vwInv vx vy hw ht hxy

end LiftAlgHom

private theorem map_modelW_zpow {K A : Type*} [CommRing K] [CommRing A] {k : ℕ}
    (φ : ModelAlgebra K k →+* A) (u : Aˣ)
    (hu : φ (coordinate K (modelIdeal K k) w) = u) (m : ℤ) :
    φ ↑(modelW K k ^ m) = ↑(u ^ m) := by
  have hmap : Units.map φ.toMonoidHom (modelW K k) = u := Units.ext hu
  exact congrArg Units.val ((map_zpow (Units.map φ.toMonoidHom) (modelW K k) m).trans (hmap ▸ rfl))

/-- Base change of `ModelAlgebra K k` along a ring homomorphism `f : K →+* K'`. -/
def mapRingHom {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') (k : ℕ) :
    ModelAlgebra K k →+* ModelAlgebra K' k :=
  liftRingHom ((algebraMap K' (ModelAlgebra K' k)).comp f)
    (coordinate K' (modelIdeal K' k) t) (coordinate K' (modelIdeal K' k) w)
    (coordinate K' (modelIdeal K' k) wInv) (coordinate K' (modelIdeal K' k) x)
    (coordinate K' (modelIdeal K' k) y) (coordinate_w_mul_wInv K' k)
    (coordinate_t_pow_succ K' k) (coordinate_x_mul_y K' k)

@[simp] theorem mapRingHom_coordinate {K K' : Type*} [CommRing K] [CommRing K']
    (f : K →+* K') (k : ℕ) (c : Coordinate) :
    mapRingHom f k (coordinate K (modelIdeal K k) c) = coordinate K' (modelIdeal K' k) c := by
  cases c <;> simp [mapRingHom]

@[simp] theorem mapRingHom_modelTheta {K K' : Type*} [CommRing K] [CommRing K']
    (f : K →+* K') (k : ℕ) (n b : ℤ) :
    mapRingHom f k (modelTheta K k n b) = modelTheta K' k n b := by
  rw [modelTheta, modelTheta, map_mul, map_modelW_zpow (mapRingHom f k) (modelW K' k) (by simp)]
  congr 1; split_ifs <;> simp [mapRingHom_coordinate]

end Universal

section Structure

variable (K : Type*) [CommRing K]

/-- Order truncation `ModelAlgebra K l →ₐ[K] ModelAlgebra K k` for `k ≤ l`. -/
def truncate {k l : ℕ} (hkl : k ≤ l) : ModelAlgebra K l →ₐ[K] ModelAlgebra K k :=
  liftAlgHom (coordinate K (modelIdeal K k) t) (coordinate K (modelIdeal K k) w)
    (coordinate K (modelIdeal K k) wInv) (coordinate K (modelIdeal K k) x)
    (coordinate K (modelIdeal K k) y) (coordinate_w_mul_wInv K k)
    (coordinate_t_pow_eq_zero_of_lt K k (Nat.lt_succ_of_le hkl)) (coordinate_x_mul_y K k)

@[simp] theorem truncate_coordinate {k l : ℕ} (hkl : k ≤ l) (c : Coordinate) :
    truncate K hkl (coordinate K (modelIdeal K l) c) = coordinate K (modelIdeal K k) c := by
  cases c <;> simp [truncate]

@[simp] theorem truncate_modelTheta {k l : ℕ} (hkl : k ≤ l) (n b : ℤ) :
    truncate K hkl (modelTheta K l n b) = modelTheta K k n b := by
  have hw := map_modelW_zpow (truncate K hkl).toRingHom (modelW K k) (by simp) b
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hw
  rw [modelTheta, modelTheta, map_mul, hw]
  congr 1; split_ifs <;> simp [truncate_coordinate]

/-! ### Focus-focus theta multiplication from `SlabAlgebra.Z_mul_Z` -/

private def modelSlabFactor (k : ℕ) : ModelAlgebra K k :=
  coordinate K (modelIdeal K k) t * (1 + coordinate K (modelIdeal K k) w)

private def evalSlab (k : ℕ) :
    SlabAlgebra (ModelAlgebra K k) (modelSlabFactor K k) →ₐ[ModelAlgebra K k] ModelAlgebra K k :=
  SlabAlgebra.lift (modelSlabFactor K k)
    (coordinate K (modelIdeal K k) x) (coordinate K (modelIdeal K k) y)
    (by rw [coordinate_x_mul_y, Algebra.algebraMap_self_apply]; rfl)

private theorem modelTheta_eq_evalSlab_Z_mul (k : ℕ) (n b : ℤ) :
    modelTheta K k n b =
      evalSlab K k (SlabAlgebra.Z (modelSlabFactor K k) n) * ↑(modelW K k ^ b) := by
  rcases Int.eq_nat_or_neg n with ⟨a, rfl | rfl⟩
  · rw [modelTheta_of_nonneg K k (Int.natCast_nonneg a), Int.natAbs_natCast,
      SlabAlgebra.Z_natCast, map_pow, evalSlab, SlabAlgebra.lift_Y]
  · rcases eq_or_ne a 0 with rfl | ha
    · simp
    · have hneg : -(a : ℤ) < 0 := Int.neg_neg_of_pos (Int.natCast_pos.mpr (Nat.pos_of_ne_zero ha))
      rw [modelTheta_of_neg K k hneg, Int.natAbs_neg, Int.natAbs_natCast,
        SlabAlgebra.Z_neg_natCast, map_pow, evalSlab, SlabAlgebra.lift_X]

/-- **Focus-focus theta multiplication**: for `r = (|n| + |m| - |n + m|) / 2`,
`ϑ_{n, b} * ϑ_{m, c} = t ^ r * ∑_{j ≤ r} binom(r, j) * ϑ_{n + m, b + c + j}` in
`ModelAlgebra K k`. -/
theorem modelTheta_mul (k : ℕ) (n m b c : ℤ) :
    let r := (n.natAbs + m.natAbs - (n + m).natAbs) / 2
    modelTheta K k n b * modelTheta K k m c =
      coordinate K (modelIdeal K k) t ^ r *
        ∑ j ∈ Finset.range (r + 1), (r.choose j : ModelAlgebra K k) *
          modelTheta K k (n + m) (b + c + j) := by
  intro r
  have hZ : evalSlab K k (SlabAlgebra.Z (modelSlabFactor K k) n *
      SlabAlgebra.Z (modelSlabFactor K k) m) =
      modelSlabFactor K k ^ r * evalSlab K k (SlabAlgebra.Z (modelSlabFactor K k) (n + m)) := by
    rw [SlabAlgebra.Z_mul_Z, map_smul, smul_eq_mul]
  have h1w : (1 + coordinate K (modelIdeal K k) w) ^ r =
      ∑ j ∈ Finset.range (r + 1), (r.choose j : ModelAlgebra K k) * ↑(modelW K k ^ (j : ℤ)) := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, zpow_natCast, Units.val_pow_eq_pow_val, modelW_val, mul_comm]
  calc
    modelTheta K k n b * modelTheta K k m c
        = evalSlab K k (SlabAlgebra.Z (modelSlabFactor K k) n *
            SlabAlgebra.Z (modelSlabFactor K k) m) * ↑(modelW K k ^ (b + c)) := by
            rw [modelTheta_eq_evalSlab_Z_mul, modelTheta_eq_evalSlab_Z_mul, map_mul,
              zpow_add, Units.val_mul]; ring
    _ = coordinate K (modelIdeal K k) t ^ r * ((1 + coordinate K (modelIdeal K k) w) ^ r *
          (evalSlab K k (SlabAlgebra.Z (modelSlabFactor K k) (n + m)) *
            ↑(modelW K k ^ (b + c)))) := by
            rw [hZ]; dsimp only [modelSlabFactor]; rw [mul_pow]; ring
    _ = coordinate K (modelIdeal K k) t ^ r *
          ∑ j ∈ Finset.range (r + 1), (r.choose j : ModelAlgebra K k) *
            modelTheta K k (n + m) (b + c + j) := by
            rw [h1w, Finset.sum_mul]; congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [modelTheta_eq_evalSlab_Z_mul, zpow_add (modelW K k) (b + c) (j : ℤ),
              Units.val_mul]; ring

/-- When the cancellation depth `r = (|n| + |m| - |n + m|) / 2` exceeds the truncation order `k`,
the theta product `ϑ_{n, b} * ϑ_{m, c}` vanishes in `ModelAlgebra K k`. -/
theorem modelTheta_mul_eq_zero_of_lt (k : ℕ) {n m : ℤ}
    (h : k < (n.natAbs + m.natAbs - (n + m).natAbs) / 2) (b c : ℤ) :
    modelTheta K k n b * modelTheta K k m c = 0 := by
  rw [modelTheta_mul, coordinate_t_pow_eq_zero_of_lt K k h, zero_mul]

/-! ### Explicit slab-algebra equivalence and `K`-basis -/

/-- The truncated deformation base ring `S_k := K[t] ⧸ (t ^ (k + 1))`. -/
abbrev BaseRing (k : ℕ) := AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)

/-- The shear wall factor `t * (1 + w)` in `LaurentPolynomial (BaseRing K k)`. -/
def modelWallFactor (k : ℕ) : LaurentPolynomial (BaseRing K k) :=
  LaurentPolynomial.C (AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)) *
    (1 + LaurentPolynomial.T 1)

theorem modelWallFactor_def (k : ℕ) :
    modelWallFactor K k =
      LaurentPolynomial.C (AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)) *
        (1 + LaurentPolynomial.T 1) := (rfl)

private abbrev SlabModel (k : ℕ) :=
  SlabAlgebra (LaurentPolynomial (BaseRing K k)) (modelWallFactor K k)

private def toModelSlab (k : ℕ) : ModelAlgebra K k →ₐ[K] SlabModel K k :=
  let φ := algebraMap (LaurentPolynomial (BaseRing K k)) (SlabModel K k)
  liftAlgHom
    (φ (LaurentPolynomial.C (AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K))))
    (φ (LaurentPolynomial.T 1)) (φ (LaurentPolynomial.T (-1)))
    (SlabAlgebra.X (modelWallFactor K k)) (SlabAlgebra.Y (modelWallFactor K k))
    (by rw [← map_mul, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      map_one])
    (by
      have h0 : AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K) ^ (k + 1) = 0 := by
        simpa using AdjoinRoot.eval₂_root (Polynomial.X ^ (k + 1) : Polynomial K)
      rw [← map_pow, ← map_pow, h0, map_zero, map_zero])
    (by rw [SlabAlgebra.X_mul_Y, ← map_one φ, ← map_add, ← map_mul]; rfl)

private def baseToModel (k : ℕ) : BaseRing K k →ₐ[K] ModelAlgebra K k :=
  AdjoinRoot.liftAlgHom (Polynomial.X ^ (k + 1)) (Algebra.ofId K (ModelAlgebra K k))
    (coordinate K (modelIdeal K k) t) (by simp [coordinate_t_pow_succ])

@[simp] private theorem baseToModel_root (k : ℕ) :
    baseToModel K k (AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)) =
      coordinate K (modelIdeal K k) t :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

private def laurentToModel (k : ℕ) : LaurentPolynomial (BaseRing K k) →ₐ[K] ModelAlgebra K k :=
  AlgHom.mk (LaurentPolynomial.eval₂ (baseToModel K k).toRingHom (modelW K k)) fun r => by
    rw [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_ofClass,
      IsScalarTower.algebraMap_apply K (BaseRing K k) (LaurentPolynomial (BaseRing K k)) r,
      ← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.eval₂_C]
    exact (baseToModel K k).commutes r

@[simp] private theorem laurentToModel_C (k : ℕ) (s : BaseRing K k) :
    laurentToModel K k (LaurentPolynomial.C s) = baseToModel K k s := by simp [laurentToModel]

@[simp] private theorem laurentToModel_T (k : ℕ) (b : ℤ) :
    laurentToModel K k (LaurentPolynomial.T b) = ↑(modelW K k ^ b) := by simp [laurentToModel]

private def fromModelSlab (k : ℕ) : SlabModel K k →ₐ[K] ModelAlgebra K k :=
  SlabAlgebra.liftAlgHom (laurentToModel K k)
    (coordinate K (modelIdeal K k) x) (coordinate K (modelIdeal K k) y)
    (by rw [coordinate_x_mul_y, modelWallFactor_def, map_mul, map_add, map_one, laurentToModel_C,
      baseToModel_root, laurentToModel_T, zpow_one, modelW_val])

private theorem toModelSlab_baseToModel (k : ℕ) (s : BaseRing K k) :
    toModelSlab K k (baseToModel K k s) =
      algebraMap (LaurentPolynomial (BaseRing K k)) (SlabModel K k) (LaurentPolynomial.C s) := by
  have heq : (toModelSlab K k).comp (baseToModel K k) =
      (IsScalarTower.toAlgHom K (LaurentPolynomial (BaseRing K k)) (SlabModel K k)).comp
        (IsScalarTower.toAlgHom K (BaseRing K k) (LaurentPolynomial (BaseRing K k))) := by
    ext
    rw [AlgHom.comp_apply, baseToModel_root, toModelSlab, liftAlgHom_coordinate_t,
      AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply,
      ← LaurentPolynomial.C_eq_algebraMap]
  simpa [AlgHom.comp_apply, ← LaurentPolynomial.C_eq_algebraMap] using AlgHom.congr_fun heq s

private theorem toModelSlab_modelW_zpow (k : ℕ) (b : ℤ) :
    toModelSlab K k ↑(modelW K k ^ b) =
      algebraMap (LaurentPolynomial (BaseRing K k)) (SlabModel K k) (LaurentPolynomial.T b) := by
  induction b using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, Units.val_mul, map_mul, ih, modelW_val, toModelSlab,
      liftAlgHom_coordinate_w, ← map_mul, ← LaurentPolynomial.T_add]
  | pred i ih =>
    rw [sub_eq_add_neg, zpow_add, zpow_neg_one, Units.val_mul, map_mul, ih, modelW_inv,
      toModelSlab, liftAlgHom_coordinate_wInv, ← map_mul, ← LaurentPolynomial.T_add]

/-- Canonical `K`-algebra equivalence between `ModelAlgebra K k` and the slab algebra
`SlabAlgebra (LaurentPolynomial (BaseRing K k)) (modelWallFactor K k)`. -/
def modelSlabEquiv (k : ℕ) :
    ModelAlgebra K k ≃ₐ[K]
      SlabAlgebra (LaurentPolynomial (BaseRing K k)) (modelWallFactor K k) :=
  AlgEquiv.ofAlgHom (toModelSlab K k) (fromModelSlab K k)
    (by
      refine SlabAlgebra.algHom_ext_of_tower (fun g => ?_)
        (by simp [toModelSlab, fromModelSlab]) (by simp [toModelSlab, fromModelSlab])
      induction g using LaurentPolynomial.induction_on' with
      | add p q hp hq =>
        simp only [AlgHom.comp_apply, AlgHom.id_apply, map_add] at hp hq ⊢; rw [hp, hq]
      | C_mul_T b s =>
        simp [fromModelSlab, toModelSlab_baseToModel, toModelSlab_modelW_zpow])
    (by ext c; cases c <;> simp [toModelSlab, fromModelSlab])

@[simp] theorem modelSlabEquiv_coordinate_t (k : ℕ) :
    modelSlabEquiv K k (coordinate K (modelIdeal K k) t) =
      algebraMap (LaurentPolynomial (BaseRing K k)) _
        (LaurentPolynomial.C (AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K))) := by
  simp [modelSlabEquiv, toModelSlab]

@[simp] theorem modelSlabEquiv_coordinate_w (k : ℕ) :
    modelSlabEquiv K k (coordinate K (modelIdeal K k) w) =
      algebraMap (LaurentPolynomial (BaseRing K k)) _ (LaurentPolynomial.T 1) := by
  simp [modelSlabEquiv, toModelSlab]

@[simp] theorem modelSlabEquiv_coordinate_wInv (k : ℕ) :
    modelSlabEquiv K k (coordinate K (modelIdeal K k) wInv) =
      algebraMap (LaurentPolynomial (BaseRing K k)) _ (LaurentPolynomial.T (-1)) := by
  simp [modelSlabEquiv, toModelSlab]

@[simp] theorem modelSlabEquiv_coordinate_x (k : ℕ) :
    modelSlabEquiv K k (coordinate K (modelIdeal K k) x) = SlabAlgebra.X (modelWallFactor K k) := by
  simp [modelSlabEquiv, toModelSlab]

@[simp] theorem modelSlabEquiv_coordinate_y (k : ℕ) :
    modelSlabEquiv K k (coordinate K (modelIdeal K k) y) = SlabAlgebra.Y (modelWallFactor K k) := by
  simp [modelSlabEquiv, toModelSlab]

@[simp] theorem modelSlabEquiv_modelTheta (k : ℕ) (n b : ℤ) :
    modelSlabEquiv K k (modelTheta K k n b) =
      algebraMap (LaurentPolynomial (BaseRing K k)) _ (LaurentPolynomial.T b) *
        SlabAlgebra.Z (modelWallFactor K k) n := by
  have hZ : modelSlabEquiv K k (if n < 0 then coordinate K (modelIdeal K k) x ^ n.natAbs
      else coordinate K (modelIdeal K k) y ^ n.natAbs) = SlabAlgebra.Z (modelWallFactor K k) n := by
    rcases Int.eq_nat_or_neg n with ⟨a, rfl | rfl⟩
    · simp [not_lt.mpr (Int.natCast_nonneg a)]
    · rcases eq_or_ne a 0 with rfl | ha
      · simp
      · simp [Nat.pos_of_ne_zero ha]
  rw [modelTheta, map_mul, hZ, mul_comm]
  exact congrArg (· * SlabAlgebra.Z (modelWallFactor K k) n) (toModelSlab_modelW_zpow K k b)

theorem modelSlabEquiv_symm_C_root_pow_mul_T_mul_Z (k r : ℕ) (n b : ℤ) :
    (modelSlabEquiv K k).symm
        (algebraMap (LaurentPolynomial (BaseRing K k)) _
          (LaurentPolynomial.C (AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K) ^ r) *
            LaurentPolynomial.T b) * SlabAlgebra.Z (modelWallFactor K k) n) =
      coordinate K (modelIdeal K k) t ^ r * modelTheta K k n b := by
  apply (modelSlabEquiv K k).injective
  rw [AlgEquiv.apply_symm_apply, map_mul (modelSlabEquiv K k), map_pow (modelSlabEquiv K k),
    modelSlabEquiv_modelTheta, modelSlabEquiv_coordinate_t, ← mul_assoc, ← map_pow, ← map_pow,
    ← map_mul]

/-- The `K`-basis `1, t, ..., t ^ k` of `BaseRing K k = K[t] ⧸ (t ^ (k + 1))`. -/
def baseRingBasis (k : ℕ) : Module.Basis (Fin (k + 1)) K (BaseRing K k) := by
  classical
  exact if hK : Nontrivial K then
    ((AdjoinRoot.powerBasis' (Polynomial.monic_X_pow (k + 1))).basis).reindex
      (finCongr (@Polynomial.natDegree_X_pow K _ hK (k + 1)))
  else
    haveI : Subsingleton K := not_nontrivial_iff_subsingleton.mp hK
    haveI : Subsingleton (BaseRing K k) := Module.subsingleton K _
    Module.Basis.ofRepr ⟨⟨⟨0, fun _ _ => Subsingleton.elim _ _⟩,
      fun _ _ => Subsingleton.elim _ _⟩, 0,
      fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

@[simp] theorem baseRingBasis_apply (k : ℕ) (i : Fin (k + 1)) :
    baseRingBasis K k i = AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K) ^ (i : ℕ) := by
  classical
  unfold baseRingBasis
  split_ifs with hK
  · simp; rfl
  · have : Subsingleton K := not_nontrivial_iff_subsingleton.mp hK
    have : Subsingleton (BaseRing K k) := Module.subsingleton K _
    exact Subsingleton.elim _ _

/-- The `K`-basis `(i, n, b) ↦ t ^ i * ϑ_{n, b}` of `ModelAlgebra K k`. -/
def modelBasis (k : ℕ) : Module.Basis (Fin (k + 1) × ℤ × ℤ) K (ModelAlgebra K k) :=
  ((((baseRingBasis K k).smulTower (AddMonoidAlgebra.basis ℤ (BaseRing K k))).smulTower
    (SlabAlgebra.basis (modelWallFactor K k))).reindex
      ((Equiv.prodAssoc (Fin (k + 1)) ℤ ℤ).trans
        (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm ℤ ℤ)))).map
    (modelSlabEquiv K k).symm.toLinearEquiv

@[simp] theorem modelBasis_apply (k : ℕ) (i : Fin (k + 1)) (n b : ℤ) :
    modelBasis K k (i, n, b) =
      coordinate K (modelIdeal K k) t ^ (i : ℕ) * modelTheta K k n b := by
  have hsmul : (AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K) ^ (i : ℕ)) •
      (LaurentPolynomial.T b : LaurentPolynomial (BaseRing K k)) =
      LaurentPolynomial.C (AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K) ^ (i : ℕ)) *
        LaurentPolynomial.T b := by rw [Algebra.smul_def, ← LaurentPolynomial.C_eq_algebraMap]
  simp only [modelBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    Module.Basis.reindex_apply, Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.refl_symm,
    Equiv.prodComm_symm, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Equiv.prodAssoc_symm_apply,
    Module.Basis.smulTower_apply, baseRingBasis_apply, AddMonoidAlgebra.basis_apply,
    SlabAlgebra.basis_apply]
  rw [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul, hsmul,
    ← one_mul (SlabAlgebra.Z (modelWallFactor K k) n), ← smul_mul_assoc,
    ← Algebra.algebraMap_eq_smul_one, modelSlabEquiv_symm_C_root_pow_mul_T_mul_Z]

/-- `ModelAlgebra K k` is a free `K`-module. -/
instance (k : ℕ) : Module.Free K (ModelAlgebra K k) :=
  Module.Free.of_basis (modelBasis K k)

/-- Over a nontrivial ring `K`, `t ^ r * ϑ_{n, b}` is nonzero in `ModelAlgebra K k` whenever
`r ≤ k`. -/
theorem pow_t_mul_modelTheta_ne_zero [Nontrivial K] (k : ℕ) {r : ℕ} (hr : r ≤ k) (n b : ℤ) :
    coordinate K (modelIdeal K k) t ^ r * modelTheta K k n b ≠ 0 := by
  have h := (modelBasis K k).ne_zero (⟨r, Nat.lt_succ_of_le hr⟩, n, b)
  rwa [modelBasis_apply] at h

/-- Over a nontrivial ring `K`, every theta element `ϑ_{n, b}` is nonzero in `ModelAlgebra K k`. -/
theorem modelTheta_ne_zero [Nontrivial K] (k : ℕ) (n b : ℤ) : modelTheta K k n b ≠ 0 := by
  simpa using pow_t_mul_modelTheta_ne_zero K k (Nat.zero_le k) n b

/-! ### Opposing-ray product check -/

/-- Explicit opposing-ray product `ϑ_{-1, b} * ϑ_{1, c} = t * (ϑ_{0, b + c} + ϑ_{0, b + c + 1})`. -/
theorem modelTheta_neg_one_mul_one (k : ℕ) (b c : ℤ) :
    modelTheta K k (-1) b * modelTheta K k 1 c =
      coordinate K (modelIdeal K k) t *
        (modelTheta K k 0 (b + c) + modelTheta K k 0 (b + c + 1)) := by
  rw [modelTheta_mul]; norm_num [Finset.sum_range_succ]

/-- Over a nontrivial ring `K`, the opposing-ray product `ϑ_{-1, b} * ϑ_{1, c}` is nonzero at
every order `1 ≤ k` (in particular for `K = ℤ`, `k = 2`). -/
theorem modelTheta_neg_one_mul_one_ne_zero [Nontrivial K] {k : ℕ} (hk : 1 ≤ k) (b c : ℤ) :
    modelTheta K k (-1) b * modelTheta K k 1 c ≠ 0 := by
  let i : Fin (k + 1) := ⟨1, Nat.lt_succ_of_le hk⟩
  intro h0
  rw [modelTheta_neg_one_mul_one, mul_add, ← pow_one (coordinate K (modelIdeal K k) t),
    ← modelBasis_apply K k i, ← modelBasis_apply K k i] at h0
  have hcoord := congrArg (fun u => (modelBasis K k).repr u (i, 0, b + c)) h0
  have hne : ((i, (0 : ℤ), b + c + 1) : Fin (k + 1) × ℤ × ℤ) ≠ (i, 0, b + c) := fun heq => by
    have := (Prod.mk.inj (Prod.mk.inj heq).2).2; omega
  rw [map_add, map_zero, Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.add_apply,
    Finsupp.zero_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne.symm, add_zero]
    at hcoord
  exact one_ne_zero hcoord

end Structure

end TauCeti.FocusFocus
