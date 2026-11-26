/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.LinearAlgebra.TensorSquare
public import TauCeti.RingTheory.MilnorK.Basic
public import TauCeti.RingTheory.MilnorK.SteinbergPairing

import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Tactic.FinCases
import TauCeti.Algebra.Module.LinearMap.Defs
import TauCeti.Algebra.Ring.Hom
import TauCeti.LinearAlgebra.TensorAlgebra.Basic
import TauCeti.LinearAlgebra.TensorAlgebra.Projection
import TauCeti.LinearAlgebra.TensorPower.Basic
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
import TauCeti.RingTheory.TwoSidedIdeal.Homogeneous
import TauCeti.RingTheory.TwoSidedIdeal.Span

/-!
# Grading and homogeneous tensor-power presentation of Milnor K-theory

The Steinberg relations generating `TauCeti.MilnorK R` are homogeneous of degree `2` in the tensor
algebra `TensorAlgebra ℤ (Additive Rˣ)`. Consequently, the kernel of the quotient map is a
homogeneous two-sided ideal, and the submodules `MilnorK.degree R n` equip `MilnorK R` with an
internal `ℕ`-grading (`GradedRing (MilnorK.degree R)`).

In each degree `n`, the kernel restricted to the `n`-th tensor power `⨂[ℤ]^n (Additive Rˣ)` is
precisely `MilnorK.tensorRel R n`, the `ℤ`-span of pure tensors containing two consecutive
complementary unit entries `(a, b)` with `(a : R) + b = 1` (equivalently, the sum over
`i + 2 + j = n` of images of `T_i ⊗ R_2 ⊗ T_j` under concatenation). This yields canonical
`ℤ`-linear equivalences:

* `MilnorK.degreeEquivQuotTensorPower n`:
  `MilnorK.degree R n ≃ₗ[ℤ] (⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n`
* `MilnorK.directSumQuotTensorPowerEquiv`:
  `(⨁ n : ℕ, (⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n) ≃ₗ[ℤ] MilnorK R`
* `MilnorK.degreeTwoEquiv : MilnorK.degree R 2 ≃ₗ[ℤ] SymbolGroup R` (complementing
  `MilnorK.degreeZeroEquiv` and `MilnorK.degreeOneEquiv` in `TauCeti.RingTheory.MilnorK.Basic`)

We also provide the graded universal property `MilnorK.gradedLift`, graded functoriality
`MilnorK.gradedMap`, concatenation `MilnorK.quotTensorPowerMul` on tensor-power quotients
compatible with homogeneous multiplication (`MilnorK.degreeEquivQuotTensorPower_mul`), and
naturality in every degree (`MilnorK.degreeEquivQuotTensorPower_map`,
`MilnorK.degreeTwoEquiv_map`).

## Main definitions

* `TauCeti.MilnorK.tensorRel`: the degree-`n` Steinberg relation submodule of
  `⨂[ℤ]^n (Additive Rˣ)`.
* `TauCeti.MilnorK.degreeEquivQuotTensorPower`: canonical identification
  `MilnorK.degree R n ≃ₗ[ℤ] (⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n`.
* `TauCeti.MilnorK.directSumQuotTensorPowerEquiv`: direct-sum identification
  `(⨁ n : ℕ, (⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n) ≃ₗ[ℤ] MilnorK R`.
* `TauCeti.MilnorK.quotTensorPowerMul`: concatenation on tensor-power quotient classes.
* `TauCeti.MilnorK.degreeTwoEquiv`: identification of degree `2` with `SymbolGroup R`.
* `TauCeti.MilnorK.gradedLift`: graded universal property for maps into any `ℕ`-graded ring.
* `TauCeti.MilnorK.gradedMap`: graded ring homomorphism induced by a ring homomorphism `R →+* S`.

## Main results

* `TauCeti.MilnorK.isSteinbergPairing_mul_ofUnit`: `(a, b) ↦ ofUnit a * ofUnit b` is a Steinberg
  pairing.
* `TauCeti.MilnorK.isHomogeneous_ker_mk`: the Steinberg two-sided ideal is homogeneous.
* `TauCeti.MilnorK.isInternal_degree`: `MilnorK R` is the internal direct sum of `MilnorK.degree R`.
* `TauCeti.MilnorK.ker_mk_comp_toTensorAlgebra`: the kernel in degree `n` equals
  `MilnorK.tensorRel R n`.
* `TauCeti.MilnorK.tensorRel_eq_iSup`: `tensorRel R n` is the sum over `i + 2 + j = n` of
  concatenated products `T_i · R_2 · T_j`.
* `TauCeti.MilnorK.degreeEquivQuotTensorPower_mul`: `degreeEquivQuotTensorPower` carries
  homogeneous multiplication to `quotTensorPowerMul`.
* `TauCeti.MilnorK.degreeTwoEquiv_map`: naturality of `degreeTwoEquiv` with respect to field and
  ring homomorphisms.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Ch. III, §7.1.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti.MilnorK

universe u v w

section Ring

variable {R : Type u} [CommRing R]

/-! ### Steinberg pairing and pure tensor helpers -/

/-- The degree-two product `(a, b) ↦ ofUnit a * ofUnit b` in `MilnorK R` is a Steinberg
pairing. -/
theorem isSteinbergPairing_mul_ofUnit :
    IsSteinbergPairing (fun a b : Rˣ ↦ ofUnit a * ofUnit b) where
  map_mul_left a₁ a₂ b := by rw [ofUnit_mul, add_mul]
  map_mul_right a b₁ b₂ := by rw [ofUnit_mul, mul_add]
  map_one_left b := by simp
  map_one_right a := by simp
  map_add_eq_one _ _ hab := ofUnit_mul_ofUnit_of_add_eq_one hab

/-- Evaluating the quotient map on a pure tensor of `Additive Rˣ` elements yields the Milnor
symbol of the underlying units. -/
theorem mk_tprod_additive {n : ℕ} (x : Fin n → Additive Rˣ) :
    mk (TensorAlgebra.tprod ℤ (Additive Rˣ) n x) = symbol (List.ofFn (Additive.toMul ∘ x)) := by
  induction n with
  | zero => simp [TensorAlgebra.tprod_apply]
  | succ n ih =>
    rw [← Fin.cons_self_tail x, TensorAlgebra.tprod_cons, map_mul, mk_ι, List.ofFn_succ,
      symbol_cons, Function.comp_apply, Fin.cons_zero]
    congr 1
    simpa [Fin.tail, Function.comp_def] using ih (Fin.tail x)

/-- Evaluating the quotient map on a pure tensor in `TensorAlgebra ℤ (Additive Rˣ)` yields the
corresponding Milnor symbol. -/
theorem mk_tprod {n : ℕ} (a : Fin n → Rˣ) :
    mk (TensorAlgebra.tprod ℤ (Additive Rˣ) n (Additive.ofMul ∘ a)) = symbol (List.ofFn a) := by
  simpa [Function.comp_def] using mk_tprod_additive (Additive.ofMul ∘ a)

/-- If an additive homomorphism out of `MilnorK R` sends every length-`n` symbol into an additive
subgroup `S`, then it maps all of `MilnorK.degree R n` into `S`. -/
theorem apply_mem_of_forall_symbol_mem {A F : Type*} {σ : Type*} [AddGroup A] [SetLike σ A]
    [AddSubgroupClass σ A] [FunLike F (MilnorK R) A] [AddMonoidHomClass F (MilnorK R) A]
    (g : F) {S : σ} {n : ℕ}
    (hg : ∀ l : List Rˣ, l.length = n → g (symbol l) ∈ S) {x : MilnorK R}
    (hx : x ∈ degree R n) : g x ∈ S := by
  rw [degree_eq_span] at hx
  refine Submodule.span_induction (p := fun y _ ↦ g y ∈ S) ?_ (by simp)
    (fun _ _ _ _ hx hy ↦ by rw [map_add]; exact add_mem hx hy)
    (fun r _ _ hx ↦ by rw [map_zsmul]; exact zsmul_mem hx r) hx
  rintro _ ⟨l, hl, rfl⟩
  exact hg l hl

/-! ### Homogeneity and the internal `ℕ`-grading -/

/-- The kernel of `MilnorK.mk` is generated as a two-sided ideal by the Steinberg products
`ι a * ι b` with `(a : R) + b = 1`. -/
theorem ker_mk_eq_span (R : Type u) [CommRing R] :
    RingHom.ker (mk (R := R)) =
      (TwoSidedIdeal.span {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧
        z = TensorAlgebra.ι ℤ (Additive.ofMul a) *
          TensorAlgebra.ι ℤ (Additive.ofMul b)}).asIdeal := by
  let I := TwoSidedIdeal.span {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧
    z = TensorAlgebra.ι ℤ (Additive.ofMul a) * TensorAlgebra.ι ℤ (Additive.ofMul b)}
  have hI : I ≤ TwoSidedIdeal.ker (mk (R := R)) := by
    refine TwoSidedIdeal.span_le.2 ?_
    rintro _ ⟨a, b, hab, rfl⟩
    exact (TwoSidedIdeal.mem_ker (mk (R := R))).2 (mk_ι_mul_ι_of_add_eq_one hab)
  have hrel : ringConGen (milnorRel R) ≤
      RingCon.ker (Ideal.Quotient.mk I.asIdeal) := by
    refine RingCon.ringConGen_le.2 ?_
    intro _ _ hrel'
    rw [milnorRel_iff] at hrel'
    rcases hrel' with ⟨a, b, hab, rfl, rfl⟩
    simp only [RingCon.ker_apply, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (TwoSidedIdeal.subset_span ⟨a, b, hab, rfl⟩)
  ext t
  constructor
  · intro ht
    rw [RingHom.mem_ker, ← map_zero (mk (R := R)), mk_eq_mk_iff] at ht
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (by simpa only [RingCon.ker_apply, map_zero] using hrel ht)
  · intro ht
    exact (TwoSidedIdeal.mem_ker (mk (R := R))).mp (hI ht)

/-- The kernel of the quotient map `TensorAlgebra ℤ (Additive Rˣ) →+* MilnorK R` is homogeneous
for Mathlib's word-length grading on the tensor algebra. -/
theorem isHomogeneous_ker_mk (R : Type u) [CommRing R] :
    (RingHom.ker (mk (R := R)).toIntAlgHom).IsHomogeneous
      (fun n : ℕ ↦ (TensorAlgebra.ι ℤ :
        Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n) := by
  have hker : RingHom.ker (mk (R := R)).toIntAlgHom = RingHom.ker (mk (R := R)) := by
    ext x
    simp [RingHom.mem_ker]
  rw [hker, ker_mk_eq_span]
  refine TwoSidedIdeal.homogeneous_span _ ?_
  rintro _ ⟨a, b, _, rfl⟩
  refine ⟨2, ?_⟩
  dsimp only
  rw [pow_two]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

/-- The degree submodules `MilnorK.degree R n` form an internal direct sum decomposition of
`MilnorK R`. -/
theorem isInternal_degree (R : Type u) [CommRing R] :
    DirectSum.IsInternal (degree R) := by
  have hdeg : degree R = fun n ↦
      Submodule.map (mk (R := R)).toIntAlgHom.toLinearMap
        ((TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n) :=
    funext fun _ ↦ Submodule.ext fun _ ↦ mem_degree_iff
  rw [hdeg]
  exact TauCeti.GradedAlgebra.isInternal_map _
    (mk (R := R)).toIntAlgHom mk_surjective (isHomogeneous_ker_mk R)

/-- `MilnorK R` is an `ℕ`-graded ring via `MilnorK.degree R`. -/
noncomputable instance instGradedRingDegree (R : Type u) [CommRing R] :
    GradedRing (degree R) :=
  { instGradedMonoidDegree with
    toDecomposition := (isInternal_degree R).chooseDecomposition }

/-! ### Graded universal property and graded functoriality -/

/-- Two graded ring homomorphisms out of `MilnorK R` agree if they agree on every `ofUnit a`. -/
theorem gradedRingHom_ext {A : Type v} {σ : Type*} [Semiring A] [SetLike σ A]
    {𝒜 : ℕ → σ} {f g : degree R →+*ᵍ 𝒜}
    (h : ∀ a : Rˣ, f (ofUnit a) = g (ofUnit a)) : f = g := by
  have hneg1 : (f : MilnorK R →+* A) (-1) = (g : MilnorK R →+* A) (-1) := calc
    (f : MilnorK R →+* A) (-1) =
        (f : MilnorK R →+* A) (-1) + ((g : MilnorK R →+* A) 1 + (g : MilnorK R →+* A) (-1)) := by
      rw [← map_add, add_neg_cancel, map_zero, add_zero]
    _ = ((f : MilnorK R →+* A) (-1) + (f : MilnorK R →+* A) 1) + (g : MilnorK R →+* A) (-1) := by
      rw [map_one, map_one, add_assoc]
    _ = (g : MilnorK R →+* A) (-1) := by
      rw [← map_add, neg_add_cancel, map_zero, zero_add]
  refine GradedRingHom.toRingHom_injective (ringHom_ext_mk (RingHom.ext fun t ↦ ?_))
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    simp only [RingHom.comp_apply, eq_intCast (algebraMap ℤ (TensorAlgebra ℤ (Additive Rˣ))) r,
      map_intCast]
    cases r with
    | ofNat n => simp
    | negSucc n =>
      rw [Int.cast_negSucc, ← neg_one_mul, map_mul, map_mul, hneg1, map_natCast, map_natCast]
  | ι x => simpa using h x.toMul
  | mul a b ha hb => simp only [RingHom.comp_apply, map_mul] at *; rw [ha, hb]
  | add a b ha hb => simp only [RingHom.comp_apply, map_add] at *; rw [ha, hb]

/-- **Graded universal property of `MilnorK R`.** An additive homomorphism `f : Additive Rˣ →+ A`
into the degree-`1` piece of an `ℕ`-graded ring whose values on complementary units multiply to
zero extends uniquely to a graded ring homomorphism `MilnorK.degree R →+*ᵍ 𝒜`. -/
def gradedLift {A : Type v} {σ : Type*} [Ring A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [SetLike.GradedMonoid 𝒜] (f : Additive Rˣ →+ A)
    (hf_deg : ∀ a : Rˣ, f (Additive.ofMul a) ∈ 𝒜 1)
    (hf_rel : ∀ a b : Rˣ, (a : R) + b = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0) :
    degree R →+*ᵍ 𝒜 where
  __ := lift f hf_rel
  map_mem hx := lift_mem_of_mem_degree f hf_rel hf_deg hx

/-- Evaluating `MilnorK.gradedLift` on `ofUnit a` recovers `f (Additive.ofMul a)`. -/
@[simp]
theorem gradedLift_ofUnit {A : Type v} {σ : Type*} [Ring A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [SetLike.GradedMonoid 𝒜] (f : Additive Rˣ →+ A)
    (hf_deg : ∀ a : Rˣ, f (Additive.ofMul a) ∈ 𝒜 1)
    (hf_rel : ∀ a b : Rˣ, (a : R) + b = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0)
    (a : Rˣ) :
    gradedLift 𝒜 f hf_deg hf_rel (ofUnit a) = f (Additive.ofMul a) :=
  lift_ofUnit f hf_rel a

/-- The underlying ring homomorphism of `MilnorK.gradedLift` is that of `MilnorK.lift`. -/
@[simp]
theorem toRingHom_gradedLift {A : Type v} {σ : Type*} [Ring A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [SetLike.GradedMonoid 𝒜] (f : Additive Rˣ →+ A)
    (hf_deg : ∀ a : Rˣ, f (Additive.ofMul a) ∈ 𝒜 1)
    (hf_rel : ∀ a b : Rˣ, (a : R) + b = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0) :
    (gradedLift 𝒜 f hf_deg hf_rel).toRingHom = lift f hf_rel :=
  ringHom_ext fun a ↦ by
    simp only [GradedRingHom.coe_toRingHom, gradedLift_ofUnit, lift_ofUnit]

/-- Evaluating `MilnorK.gradedLift` on a symbol multiplies the images of its entries. -/
@[simp]
theorem gradedLift_symbol {A : Type v} {σ : Type*} [Ring A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [SetLike.GradedMonoid 𝒜] (f : Additive Rˣ →+ A)
    (hf_deg : ∀ a : Rˣ, f (Additive.ofMul a) ∈ 𝒜 1)
    (hf_rel : ∀ a b : Rˣ, (a : R) + b = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0)
    (l : List Rˣ) :
    gradedLift 𝒜 f hf_deg hf_rel (symbol l) = (l.map fun a ↦ f (Additive.ofMul a)).prod :=
  lift_symbol f hf_rel l

/-- Functoriality of `MilnorK` as a graded ring homomorphism `degree R →+*ᵍ degree S`. -/
def gradedMap {S : Type w} [CommRing S] (f : R →+* S) : degree R →+*ᵍ degree S where
  __ := map f
  map_mem hx := map_mem_degree f hx

/-- Evaluating `MilnorK.gradedMap f` on `ofUnit a` gives `ofUnit (Units.map f a)`. -/
@[simp]
theorem gradedMap_ofUnit {S : Type w} [CommRing S] (f : R →+* S) (a : Rˣ) :
    gradedMap f (ofUnit a) = ofUnit (Units.map f.toMonoidHom a) :=
  map_ofUnit f a

/-- The underlying ring homomorphism of `MilnorK.gradedMap f` is that of `MilnorK.map f`. -/
@[simp]
theorem toRingHom_gradedMap {S : Type w} [CommRing S] (f : R →+* S) :
    (gradedMap f).toRingHom = map f :=
  ringHom_ext fun a ↦ by
    simp only [GradedRingHom.coe_toRingHom, gradedMap_ofUnit, map_ofUnit,
      RingHom.toMonoidHom_eq_coe]

/-- Evaluating `MilnorK.gradedMap f` on a symbol maps its entries in unchanged order. -/
@[simp]
theorem gradedMap_symbol {S : Type w} [CommRing S] (f : R →+* S) (l : List Rˣ) :
    gradedMap f (symbol l) = symbol (l.map (Units.map f.toMonoidHom)) :=
  map_symbol f l

/-- The identity ring homomorphism induces the identity graded ring homomorphism on `MilnorK`. -/
@[simp]
theorem gradedMap_id (R : Type u) [CommRing R] :
    gradedMap (RingHom.id R) = GradedRingHom.id (degree R) :=
  gradedRingHom_ext fun a ↦ by simp

/-- `MilnorK.gradedMap` respects composition of ring homomorphisms. -/
theorem gradedMap_comp {S : Type v} {T : Type w} [CommRing S] [CommRing T]
    (g : S →+* T) (f : R →+* S) :
    gradedMap (g.comp f) = (gradedMap g).comp (gradedMap f) :=
  gradedRingHom_ext fun a ↦ by
    simp only [gradedMap_ofUnit, GradedRingHom.comp_apply, RingHom.toMonoidHom_comp,
      Units.map_comp, MonoidHom.comp_apply]

end Ring

/-! ### The degree-`n` Steinberg relation submodule -/

section TensorRel

variable {R : Type u} [CommSemiring R]

variable (R)

/-- The degree-`n` Steinberg relation submodule `R_n ⊆ ⨂[ℤ]^n (Additive Rˣ)`: the `ℤ`-span of
pure tensors having two consecutive entries `Additive.ofMul a`, `Additive.ofMul b` with
`(a : R) + b = 1`. -/
def tensorRel (n : ℕ) : Submodule ℤ (⨂[ℤ]^n (Additive Rˣ)) :=
  Submodule.span ℤ
    {t | ∃ (x : Fin n → Additive Rˣ) (k : ℕ) (hk : k + 1 < n) (a b : Rˣ), (a : R) + b = 1 ∧
      x ⟨k, by omega⟩ = Additive.ofMul a ∧ x ⟨k + 1, hk⟩ = Additive.ofMul b ∧
      t = PiTensorProduct.tprod ℤ x}

/-- Unfolding lemma for `MilnorK.tensorRel`. -/
theorem tensorRel_eq_span (n : ℕ) :
    tensorRel R n = Submodule.span ℤ
      {t | ∃ (x : Fin n → Additive Rˣ) (k : ℕ) (hk : k + 1 < n) (a b : Rˣ), (a : R) + b = 1 ∧
        x ⟨k, by omega⟩ = Additive.ofMul a ∧ x ⟨k + 1, hk⟩ = Additive.ofMul b ∧
        t = PiTensorProduct.tprod ℤ x} := by
  rw [tensorRel]

/-- In degree `0`, the Steinberg relation submodule is trivial. -/
@[simp]
theorem tensorRel_zero : tensorRel R 0 = ⊥ := by
  rw [tensorRel, Submodule.span_eq_bot]; rintro _ ⟨_, _, hk, _⟩; omega

/-- In degree `1`, the Steinberg relation submodule is trivial. -/
@[simp]
theorem tensorRel_one : tensorRel R 1 = ⊥ := by
  rw [tensorRel, Submodule.span_eq_bot]; rintro _ ⟨_, _, hk, _⟩; omega

variable {R}

/-- Casting the degree of a tensor power preserves membership in `tensorRel`. -/
theorem cast_mem_tensorRel {m n : ℕ} (h : m = n) {u : ⨂[ℤ]^m (Additive Rˣ)}
    (hu : u ∈ tensorRel R m) : TensorPower.cast ℤ (Additive Rˣ) h u ∈ tensorRel R n := by
  subst h; simpa using hu

/-- A pure degree-two tensor of complementary units lies in `tensorRel R 2`. -/
theorem tprod_pair_mem_tensorRel {a b : Rˣ} (hab : (a : R) + b = 1) :
    PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b] ∈ tensorRel R 2 :=
  Submodule.subset_span
    ⟨![Additive.ofMul a, Additive.ofMul b], 0, by decide, a, b, hab, rfl, rfl, rfl⟩

private theorem gMul_mem_tensorRel_of_generators {i j : ℕ} {s₁ : Set (⨂[ℤ]^i (Additive Rˣ))}
    {s₂ : Set (⨂[ℤ]^j (Additive Rˣ))} {u : ⨂[ℤ]^i (Additive Rˣ)} {v : ⨂[ℤ]^j (Additive Rˣ)}
    (hu : u ∈ Submodule.span ℤ s₁) (hv : v ∈ Submodule.span ℤ s₂)
    (h : ∀ x ∈ s₁, ∀ y ∈ s₂,
      GradedMonoid.GMul.mul (A := fun m ↦ ⨂[ℤ]^m (Additive Rˣ)) x y ∈ tensorRel R (i + j)) :
    GradedMonoid.GMul.mul (A := fun m ↦ ⨂[ℤ]^m (Additive Rˣ)) u v ∈ tensorRel R (i + j) := by
  have hle : Submodule.map₂
      ((TensorProduct.mk ℤ _ _).compr₂ (TensorPower.mulEquiv : _ ≃ₗ[ℤ] _).toLinearMap)
      (Submodule.span ℤ s₁) (Submodule.span ℤ s₂) ≤ tensorRel R (i + j) := by
    rw [Submodule.map₂_span_span, Submodule.span_le, Set.image2_subset_iff]
    intro x hx y hy
    rw [← TensorPower.gMul_eq_coe_linearMap]
    exact h x hx y hy
  rw [TensorPower.gMul_eq_coe_linearMap]
  exact hle (Submodule.apply_mem_map₂ _ hu hv)

/-- Right concatenation preserves the Steinberg relation submodule (`R_i · T_j ⊆ R_{i+j}`). -/
theorem gMul_mem_tensorRel_left {i j : ℕ} {u : ⨂[ℤ]^i (Additive Rˣ)} {v : ⨂[ℤ]^j (Additive Rˣ)}
    (hu : u ∈ tensorRel R i) :
    GradedMonoid.GMul.mul (A := fun m ↦ ⨂[ℤ]^m (Additive Rˣ)) u v ∈ tensorRel R (i + j) := by
  refine gMul_mem_tensorRel_of_generators hu (PiTensorProduct.span_tprod_eq_top.ge trivial) ?_
  rintro _ ⟨x, k, hk, a, b, hab, hxk, hxk1, rfl⟩ _ ⟨y, rfl⟩
  rw [TensorPower.tprod_mul_tprod]
  exact Submodule.subset_span ⟨Fin.append x y, k, by omega, a, b, hab,
    (Fin.append_left x y ⟨k, by omega⟩).trans hxk,
    (Fin.append_left x y ⟨k + 1, hk⟩).trans hxk1, rfl⟩

/-- Left concatenation preserves the Steinberg relation submodule (`T_i · R_j ⊆ R_{i+j}`). -/
theorem gMul_mem_tensorRel_right {i j : ℕ} {u : ⨂[ℤ]^i (Additive Rˣ)} {v : ⨂[ℤ]^j (Additive Rˣ)}
    (hv : v ∈ tensorRel R j) :
    GradedMonoid.GMul.mul (A := fun m ↦ ⨂[ℤ]^m (Additive Rˣ)) u v ∈ tensorRel R (i + j) := by
  refine gMul_mem_tensorRel_of_generators (PiTensorProduct.span_tprod_eq_top.ge trivial) hv ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, k, hk, a, b, hab, hyk, hyk1, rfl⟩
  rw [TensorPower.tprod_mul_tprod]
  refine Submodule.subset_span ⟨Fin.append x y, i + k, by omega, a, b, hab,
    (Fin.append_right x y ⟨k, by omega⟩).trans hyk, ?_, rfl⟩
  have h2 : (⟨i + k + 1, by omega⟩ : Fin (i + j)) = Fin.natAdd i ⟨k + 1, hk⟩ :=
    Fin.ext (by dsimp; omega)
  rw [h2, Fin.append_right, hyk1]

/-- The degree-`n` Steinberg relation submodule `R_n` is the sum over `i + 2 + j = n` of the
images of `T_i · R_2 · T_j` under concatenation. -/
theorem tensorRel_eq_iSup (R : Type u) [CommSemiring R] (n : ℕ) :
    tensorRel R n =
      ⨆ (i : ℕ) (j : ℕ) (h : i + 2 + j = n),
        Submodule.span ℤ
          {w | ∃ (u : ⨂[ℤ]^i (Additive Rˣ)) (r : ⨂[ℤ]^2 (Additive Rˣ)), r ∈ tensorRel R 2 ∧
            ∃ v : ⨂[ℤ]^j (Additive Rˣ), w = TensorPower.cast ℤ (Additive Rˣ) h
              (GradedMonoid.GMul.mul (A := fun m ↦ ⨂[ℤ]^m (Additive Rˣ))
                (GradedMonoid.GMul.mul (A := fun m ↦ ⨂[ℤ]^m (Additive Rˣ)) u r) v)} := by
  refine le_antisymm ?_ (iSup_le fun i ↦ iSup_le fun j ↦ iSup_le fun h ↦ Submodule.span_le.mpr ?_)
  · rw [tensorRel, Submodule.span_le]
    rintro _ ⟨x, k, hk, a, b, hab, hxk, hxk1, rfl⟩
    have hsum : k + 2 + (n - (k + 2)) = n := by omega
    refine Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem (n - (k + 2))
      (Submodule.mem_iSup_of_mem hsum (Submodule.subset_span ?_)))
    let y : Fin (k + 2 + (n - (k + 2))) → Additive Rˣ := x ∘ Fin.cast hsum
    have hmid : ![Additive.ofMul a, Additive.ofMul b] =
        fun j : Fin 2 ↦ y (Fin.castAdd (n - (k + 2)) (Fin.natAdd k j)) := by
      funext j; fin_cases j <;> [exact hxk.symm; exact hxk1.symm]
    refine ⟨PiTensorProduct.tprod ℤ (fun p : Fin k ↦ y (Fin.castAdd _ (Fin.castAdd 2 p))),
      PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b],
      tprod_pair_mem_tensorRel hab,
      PiTensorProduct.tprod ℤ (fun q : Fin (n - (k + 2)) ↦ y (Fin.natAdd (k + 2) q)), ?_⟩
    rw [hmid, TensorPower.tprod_mul_tprod, TensorPower.tprod_mul_tprod,
      Fin.append_castAdd_natAdd (f := fun i ↦ y (Fin.castAdd _ i)),
      Fin.append_castAdd_natAdd (f := y), TensorPower.cast_tprod]
    exact congrArg (PiTensorProduct.tprod ℤ) (funext fun i ↦ by simp [y])
  · rintro _ ⟨u, r, hr, v, rfl⟩
    exact cast_mem_tensorRel h (gMul_mem_tensorRel_left (gMul_mem_tensorRel_right hr))

/-- Under `TauCeti.tensorProductEquivTensorSquare`, the binary Steinberg relation submodule
`steinbergRelations R` corresponds exactly to `MilnorK.tensorRel R 2`. -/
theorem map_steinbergRelations_eq_tensorRel_two (R : Type u) [CommSemiring R] :
    (steinbergRelations R).map
      (TauCeti.tensorProductEquivTensorSquare ℤ (Additive Rˣ)).toLinearMap =
      tensorRel R 2 := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    rw [steinbergRelations_eq_span] at ht
    refine Submodule.span_induction
      (p := fun t _ ↦ (TauCeti.tensorProductEquivTensorSquare ℤ (Additive Rˣ)) t ∈ tensorRel R 2)
      ?_ (by simp) (fun _ _ _ _ hx hy ↦ by rw [map_add]; exact add_mem hx hy)
      (fun r _ _ hx ↦ by rw [map_zsmul]; exact zsmul_mem hx r) ht
    rintro _ ⟨a, b, hab, rfl⟩
    rw [TauCeti.tensorProductEquivTensorSquare_tmul]
    exact tprod_pair_mem_tensorRel hab
  · rw [tensorRel, Submodule.span_le]
    rintro _ ⟨x, k, hk, a, b, hab, hxk, hxk1, rfl⟩
    have hk0 : k = 0 := by omega
    subst hk0
    have hx : x = ![Additive.ofMul a, Additive.ofMul b] :=
      funext fun i ↦ by fin_cases i <;> [exact hxk; exact hxk1]
    rw [hx]
    refine ⟨Additive.ofMul a ⊗ₜ Additive.ofMul b, ?_,
      TauCeti.tensorProductEquivTensorSquare_tmul ℤ (Additive Rˣ) _ _⟩
    rw [steinbergRelations_eq_span]
    exact Submodule.subset_span ⟨a, b, hab, rfl⟩

/-- Pointwise `AddCommMonoid` instance aiding `DirectSum` typeclass synthesis over `ℕ`. -/
instance (priority := low) instAddCommMonoidQuotTensorPower (R : Type u) [CommSemiring R]
    (n : ℕ) : AddCommMonoid ((⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n) :=
  inferInstance

/-- Pointwise `Module ℤ` instance aiding `DirectSum` typeclass synthesis over `ℕ`. -/
instance (priority := low) instModuleQuotTensorPower (R : Type u) [CommSemiring R] (n : ℕ) :
    Module ℤ ((⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n) :=
  inferInstance

/-- Concatenation of tensor-power quotient classes, descending graded tensor-power
multiplication modulo `tensorRel`. -/
noncomputable def quotTensorPowerMul (R : Type u) [CommSemiring R] (i j : ℕ) :
    ((⨂[ℤ]^i (Additive Rˣ)) ⧸ tensorRel R i) →ₗ[ℤ]
      ((⨂[ℤ]^j (Additive Rˣ)) ⧸ tensorRel R j) →ₗ[ℤ]
      ((⨂[ℤ]^(i + j) (Additive Rˣ)) ⧸ tensorRel R (i + j)) :=
  LinearMap.liftQ₂ (tensorRel R i) (tensorRel R j)
    ((TensorProduct.mk ℤ _ _).compr₂
      ((tensorRel R (i + j)).mkQ.comp (TensorPower.mulEquiv : _ ≃ₗ[ℤ] _).toLinearMap))
    (fun _ hu ↦ LinearMap.mem_ker.mpr <| LinearMap.ext fun _ ↦
      (Submodule.Quotient.mk_eq_zero _).mpr (gMul_mem_tensorRel_left hu))
    (fun _ hv ↦ LinearMap.mem_ker.mpr <| LinearMap.ext fun _ ↦
      (Submodule.Quotient.mk_eq_zero _).mpr (gMul_mem_tensorRel_right hv))

/-- `quotTensorPowerMul` acts on quotient representatives by graded tensor-power
multiplication. -/
@[simp]
theorem quotTensorPowerMul_mk {i j : ℕ} (u : ⨂[ℤ]^i (Additive Rˣ))
    (v : ⨂[ℤ]^j (Additive Rˣ)) :
    quotTensorPowerMul R i j (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk
        (GradedMonoid.GMul.mul (A := fun m ↦ ⨂[ℤ]^m (Additive Rˣ)) u v) := by
  simp [quotTensorPowerMul, TensorPower.gMul_def]

end TensorRel

/-! ### The homogeneous Steinberg quotient bridge -/

section Bridge

variable {R : Type u} [CommRing R]

/-- Projecting any two-sided ideal multiple `p * (ι a * ι b) * q` of a Steinberg generator into
degree `n` lands in `MilnorK.tensorRel R n`. -/
private theorem tensorPowerProjection_mul_steinberg_mul_mem_tensorRel {n : ℕ}
    (p q : TensorAlgebra ℤ (Additive Rˣ)) {a b : Rˣ} (hab : (a : R) + b = 1) :
    TensorAlgebra.tensorPowerProjection n
      (p * (TensorAlgebra.ι ℤ (Additive.ofMul a) * TensorAlgebra.ι ℤ (Additive.ofMul b)) * q) ∈
      tensorRel R n := by
  rw [← TensorAlgebra.ofDirectSum_toDirectSum p, ← TensorAlgebra.ofDirectSum_toDirectSum q]
  generalize TensorAlgebra.toDirectSum p = p'
  generalize TensorAlgebra.toDirectSum q = q'
  induction p' using DirectSum.induction_on with
  | zero => simp
  | add p₁ p₂ hp₁ hp₂ => rw [map_add, add_mul, add_mul, map_add]; exact add_mem hp₁ hp₂
  | of i u =>
    induction q' using DirectSum.induction_on with
    | zero => simp
    | add q₁ q₂ hq₁ hq₂ => rw [map_add, mul_add, map_add]; exact add_mem hq₁ hq₂
    | of j v =>
      have hmid : TensorAlgebra.ι ℤ (Additive.ofMul a) * TensorAlgebra.ι ℤ (Additive.ofMul b) =
          TensorPower.toTensorAlgebra (R := ℤ) (M := Additive Rˣ)
            (PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b]) := by
        simp [TensorAlgebra.tprod_apply]
      rw [TensorAlgebra.ofDirectSum_of, TensorAlgebra.ofDirectSum_of, hmid,
        ← TensorPower.toTensorAlgebra_gMul, ← TensorPower.toTensorAlgebra_gMul]
      have hw := gMul_mem_tensorRel_left (v := v)
        (gMul_mem_tensorRel_right (u := u) (tprod_pair_mem_tensorRel hab))
      by_cases hdeg : i + 2 + j = n
      · subst hdeg; rw [TensorAlgebra.tensorPowerProjection_toTensorAlgebra]; exact hw
      · rw [TensorAlgebra.tensorPowerProjection_of_mem_range_pow_ne hdeg
          (TensorPower.toTensorAlgebra_mem_range_pow _ _)]; exact zero_mem _

private theorem mem_ker_mk_comp_toTensorAlgebra_iff {n : ℕ} {w : ⨂[ℤ]^n (Additive Rˣ)} :
    w ∈ LinearMap.ker
      ((mk (R := R)).toIntAlgHom.toLinearMap.comp
        (TensorPower.toTensorAlgebra (R := ℤ) (M := Additive Rˣ) (n := n))) ↔
      TensorPower.toTensorAlgebra w ∈ RingHom.ker (mk (R := R)) := by
  simp

/-- **Homogeneous kernel identification.** The kernel of the quotient map
`TensorPower ℤ n (Additive Rˣ) → TensorAlgebra ℤ (Additive Rˣ) → MilnorK R` is exactly
`MilnorK.tensorRel R n`. -/
theorem ker_mk_comp_toTensorAlgebra (R : Type u) [CommRing R] (n : ℕ) :
    LinearMap.ker
      ((mk (R := R)).toIntAlgHom.toLinearMap.comp
        (TensorPower.toTensorAlgebra (R := ℤ) (M := Additive Rˣ) (n := n))) =
      tensorRel R n := by
  refine le_antisymm ?_ ?_
  · intro w hw
    rw [mem_ker_mk_comp_toTensorAlgebra_iff, ker_mk_eq_span] at hw
    let H : Submodule ℤ (TensorAlgebra ℤ (Additive Rˣ)) :=
      (tensorRel R n).comap (TensorAlgebra.tensorPowerProjection n)
    have hsub :
        (TwoSidedIdeal.span {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧
          z = TensorAlgebra.ι ℤ (Additive.ofMul a) * TensorAlgebra.ι ℤ (Additive.ofMul b)} :
          Set (TensorAlgebra ℤ (Additive Rˣ))) ⊆ H.toAddSubgroup := by
      rw [TauCeti.TwoSidedIdeal.coe_span_subset_addSubgroup_iff]
      rintro p _ ⟨a, b, hab, rfl⟩ q
      exact tensorPowerProjection_mul_steinberg_mul_mem_tensorRel p q hab
    have hwH : TensorPower.toTensorAlgebra w ∈ H := hsub hw
    rw [Submodule.mem_comap, TensorAlgebra.tensorPowerProjection_toTensorAlgebra] at hwH
    exact hwH
  · rw [tensorRel, Submodule.span_le]
    rintro _ ⟨x, k, hk, a, b, hab, hxk, hxk1, rfl⟩
    rw [SetLike.mem_coe, mem_ker_mk_comp_toTensorAlgebra_iff, RingHom.mem_ker,
      TensorPower.toTensorAlgebra_tprod, mk_tprod_additive]
    set l : List Rˣ := List.ofFn (Additive.toMul ∘ x)
    have hlen : l.length = n := List.length_ofFn
    have hsplit : l = l.take k ++ a :: b :: l.drop (k + 2) := by
      conv_lhs =>
        rw [← List.take_append_drop k l, List.drop_eq_getElem_cons (by omega),
          List.drop_eq_getElem_cons (by omega)]
      simp [l, hxk, hxk1]
    rw [hsplit]
    exact symbol_append_cons_cons_of_add_eq_one _ _ hab

/-- Intersecting the Steinberg kernel with the degree-`n` piece of the tensor algebra yields the
image of `tensorRel R n`. -/
theorem ker_mk_inf_range_pow (R : Type u) [CommRing R] (n : ℕ) :
    LinearMap.ker (mk (R := R)).toIntAlgHom.toLinearMap ⊓
        (TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n =
      (tensorRel R n).map (TensorPower.toTensorAlgebra (R := ℤ) (M := Additive Rˣ) (n := n)) := by
  rw [← ker_mk_comp_toTensorAlgebra R n, LinearMap.ker_comp, Submodule.map_comap_eq,
    TensorPower.range_toTensorAlgebra, inf_comm]

/-- The canonical linear map from `⨂[ℤ]^n (Additive Rˣ)` onto `MilnorK.degree R n`. -/
private noncomputable def tensorPowerToDegree (R : Type u) [CommRing R] (n : ℕ) :
    (⨂[ℤ]^n (Additive Rˣ)) →ₗ[ℤ] degree R n :=
  ((mk (R := R)).toIntAlgHom.toLinearMap.comp
    (TensorPower.toTensorAlgebra (R := ℤ) (M := Additive Rˣ) (n := n))).codRestrict (degree R n)
    fun w ↦ mem_degree_iff.mpr
      ⟨TensorPower.toTensorAlgebra w, TensorPower.toTensorAlgebra_mem_range_pow n w, rfl⟩

@[simp]
private theorem coe_tensorPowerToDegree (R : Type u) [CommRing R] (n : ℕ)
    (w : ⨂[ℤ]^n (Additive Rˣ)) :
    (tensorPowerToDegree R n w : MilnorK R) =
      mk (TensorPower.toTensorAlgebra w) := by
  simp only [tensorPowerToDegree, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_apply]

private theorem tensorPowerToDegree_surjective (R : Type u) [CommRing R] (n : ℕ) :
    Function.Surjective (tensorPowerToDegree R n) := by
  rintro ⟨x, hx⟩
  rw [mem_degree_iff] at hx
  rcases hx with ⟨t, ht, rfl⟩
  rw [← TensorPower.range_toTensorAlgebra] at ht
  rcases ht with ⟨w, rfl⟩
  exact ⟨w, Subtype.ext (coe_tensorPowerToDegree R n w)⟩

private theorem ker_tensorPowerToDegree (R : Type u) [CommRing R] (n : ℕ) :
    LinearMap.ker (tensorPowerToDegree R n) = tensorRel R n := by
  rw [tensorPowerToDegree, LinearMap.ker_codRestrict, ker_mk_comp_toTensorAlgebra]

/-- **The homogeneous Steinberg quotient bridge.** In every degree `n`, the degree-`n` Milnor
group is canonically isomorphic to `(⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n`. -/
noncomputable def degreeEquivQuotTensorPower (R : Type u) [CommRing R] (n : ℕ) :
    degree R n ≃ₗ[ℤ] (⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n :=
  ((Submodule.quotEquivOfEq (tensorRel R n) _ (ker_tensorPowerToDegree R n).symm).trans
    ((tensorPowerToDegree R n).quotKerEquivOfSurjective
      (tensorPowerToDegree_surjective R n))).symm

/-- The inverse of `degreeEquivQuotTensorPower` sends the class of a tensor `w` to the image
of `TensorPower.toTensorAlgebra w` in `MilnorK R`. -/
theorem coe_degreeEquivQuotTensorPower_symm_mk {n : ℕ} (w : ⨂[ℤ]^n (Additive Rˣ)) :
    ((degreeEquivQuotTensorPower R n).symm (Submodule.Quotient.mk w) : MilnorK R) =
      mk (TensorPower.toTensorAlgebra w) := by
  simp [degreeEquivQuotTensorPower]

/-- The inverse of `degreeEquivQuotTensorPower` sends the class of a pure tensor to the
corresponding Milnor symbol. -/
@[simp]
theorem coe_degreeEquivQuotTensorPower_symm_mk_tprod {n : ℕ} (a : Fin n → Rˣ) :
    ((degreeEquivQuotTensorPower R n).symm
      (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ a))) : MilnorK R) =
      symbol (List.ofFn a) := by
  rw [coe_degreeEquivQuotTensorPower_symm_mk, TensorPower.toTensorAlgebra_tprod, mk_tprod]

/-- `degreeEquivQuotTensorPower` sends any degree-`n` class equal to `symbol (List.ofFn a)` to
the class of its pure tensor. -/
theorem degreeEquivQuotTensorPower_of_coe_eq_symbol {n : ℕ} (x : degree R n) (a : Fin n → Rˣ)
    (hx : (x : MilnorK R) = symbol (List.ofFn a)) :
    degreeEquivQuotTensorPower R n x =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ a)) := by
  apply (degreeEquivQuotTensorPower R n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact Subtype.ext (hx.trans (coe_degreeEquivQuotTensorPower_symm_mk_tprod a).symm)

/-- `degreeEquivQuotTensorPower` sends a Milnor symbol to the class of its pure tensor. -/
@[simp]
theorem degreeEquivQuotTensorPower_symbol {n : ℕ} (a : Fin n → Rˣ) :
    degreeEquivQuotTensorPower R n
      ⟨symbol (List.ofFn a),
        by simpa only [List.length_ofFn] using symbol_mem_degree (List.ofFn a)⟩ =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ a)) :=
  degreeEquivQuotTensorPower_of_coe_eq_symbol _ a rfl

/-- **Direct-sum tensor-power presentation of `MilnorK R`.** `MilnorK R` is canonically
isomorphic as a `ℤ`-module to the direct sum of the degree-`n` tensor-power quotients
`(⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n`. -/
noncomputable def directSumQuotTensorPowerEquiv (R : Type u) [CommRing R] :
    (⨁ n : ℕ, (⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n) ≃ₗ[ℤ] MilnorK R :=
  (DirectSum.congrLinearEquiv fun n ↦ (degreeEquivQuotTensorPower R n).symm).trans
    (DirectSum.decomposeLinearEquiv (degree R)).symm

/-- Evaluating `directSumQuotTensorPowerEquiv` on a single summand recovers the canonical
inclusion of that degree into `MilnorK R`. -/
@[simp]
theorem directSumQuotTensorPowerEquiv_of (n : ℕ)
    (x : (⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n) :
    directSumQuotTensorPowerEquiv R (DirectSum.of _ n x) =
      ((degreeEquivQuotTensorPower R n).symm x : MilnorK R) := by
  rw [directSumQuotTensorPowerEquiv, LinearEquiv.trans_apply, DirectSum.coe_congrLinearEquiv,
    ← DirectSum.lof_eq_of ℤ, DirectSum.lmap_lof]
  exact DirectSum.decompose_symm_of (degree R) _

/-- `degreeEquivQuotTensorPower` carries homogeneous multiplication in `MilnorK R` to
concatenation `quotTensorPowerMul` on tensor-power quotient classes. -/
theorem degreeEquivQuotTensorPower_mul {i j : ℕ} (x : degree R i) (y : degree R j) :
    degreeEquivQuotTensorPower R (i + j)
      ⟨(x : MilnorK R) * y, SetLike.GradedMul.mul_mem x.property y.property⟩ =
      quotTensorPowerMul R i j
        (degreeEquivQuotTensorPower R i x) (degreeEquivQuotTensorPower R j y) := by
  obtain ⟨x', rfl⟩ := (degreeEquivQuotTensorPower R i).symm.surjective x
  obtain ⟨y', rfl⟩ := (degreeEquivQuotTensorPower R j).symm.surjective y
  induction x' using Submodule.Quotient.induction_on with | _ u =>
  induction y' using Submodule.Quotient.induction_on with | _ v =>
  refine (degreeEquivQuotTensorPower R (i + j)).symm.injective (Subtype.ext ?_)
  simp only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, quotTensorPowerMul_mk,
    coe_degreeEquivQuotTensorPower_symm_mk, TensorPower.toTensorAlgebra_gMul, map_mul]

/-! ### Degree-two identification `K₂ᴹ ≃ SymbolGroup R` -/

/-- Canonical identification `MilnorK.degree R 2 ≃ₗ[ℤ] SymbolGroup R`. -/
noncomputable def degreeTwoEquiv (R : Type u) [CommRing R] :
    degree R 2 ≃ₗ[ℤ] SymbolGroup R :=
  (degreeEquivQuotTensorPower R 2).trans
    (Submodule.Quotient.equiv (steinbergRelations R) (tensorRel R 2)
      -- Re-synthesize `[Ring ℤ]` / `AddCommGroup.toIntModule` instances expected by
      -- `Submodule.Quotient.equiv` at `implicit` transparency (unlike
      -- `tensorProductEquivTensorSquare`, which carries `[CommSemiring ℤ]` and
      -- `TensorProduct.instModule` / `PiTensorProduct.instModule`).
      (TauCeti.tensorProductEquivTensorSquare ℤ (Additive Rˣ)).toAddEquiv.toIntLinearEquiv
      (by
        -- Both `Submodule.map` applications agree definitionally (same underlying map, differing
        -- only in those `ℤ`-module instance wrappers).
        rw [← map_steinbergRelations_eq_tensorRel_two R]
        congr 1)).symm

/-- `degreeTwoEquiv` sends the product `ofUnit a * ofUnit b` to `SymbolGroup.symbol a b`. -/
@[simp]
theorem degreeTwoEquiv_ofUnit_mul (a b : Rˣ) :
    degreeTwoEquiv R
      ⟨ofUnit a * ofUnit b,
        SetLike.GradedMul.mul_mem (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩ =
      SymbolGroup.symbol a b := by
  have h := degreeEquivQuotTensorPower_of_coe_eq_symbol
    ⟨ofUnit a * ofUnit b,
      SetLike.GradedMul.mul_mem (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩
    ![a, b] (by simp)
  simp [degreeTwoEquiv, h, AddEquiv.coe_symm_toIntLinearEquiv]

/-- The inverse of `degreeTwoEquiv` sends `SymbolGroup.symbol a b` to `ofUnit a * ofUnit b`. -/
@[simp]
theorem coe_degreeTwoEquiv_symm_symbol (a b : Rˣ) :
    ((degreeTwoEquiv R).symm (SymbolGroup.symbol a b) : MilnorK R) = ofUnit a * ofUnit b := by
  simpa only [degreeTwoEquiv_ofUnit_mul] using congrArg Subtype.val
    ((degreeTwoEquiv R).symm_apply_apply
      ⟨ofUnit a * ofUnit b,
        SetLike.GradedMul.mul_mem (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩)

/-- Naturality of `degreeTwoEquiv`: for any ring homomorphism `f : R →+* S`, the degree-`2`
restriction of `MilnorK.map f` corresponds to `SymbolGroup.map f`. -/
theorem degreeTwoEquiv_map {S : Type w} [CommRing S] (f : R →+* S) (x : degree R 2) :
    degreeTwoEquiv S ⟨map f x, map_mem_degree f x.property⟩ =
      SymbolGroup.map f (degreeTwoEquiv R x) := by
  obtain ⟨y, rfl⟩ := (degreeTwoEquiv R).symm.surjective x
  refine (degreeTwoEquiv S).symm.injective (Subtype.ext ?_)
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  dsimp only
  induction y using SymbolGroup.induction_on with
  | symbol a b => simp
  | add y₁ y₂ hy₁ hy₂ => simp only [map_add, Submodule.coe_add, hy₁, hy₂]

end Bridge

/-! ### Arbitrary-degree naturality -/

/-- Applying a ring homomorphism entrywise on `⨂[ℤ]^n (Additive Rˣ)` preserves `tensorRel`. -/
theorem map_tensorRel_le {R : Type u} [CommSemiring R] {S : Type w} [CommSemiring S]
    (f : R →+* S) (n : ℕ) :
    (tensorRel R n).map (PiTensorProduct.map fun _ : Fin n ↦
        (Units.map f.toMonoidHom).toAdditive.toIntLinearMap) ≤ tensorRel S n := by
  rw [Submodule.map_le_iff_le_comap, tensorRel, Submodule.span_le]
  rintro _ ⟨x, k, hk, a, b, hab, hxk, hxk1, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, PiTensorProduct.map_tprod]
  exact Submodule.subset_span ⟨_, k, hk, Units.map f.toMonoidHom a, Units.map f.toMonoidHom b,
    by simp [← map_add, hab], by simp [hxk], by simp [hxk1], rfl⟩

/-- Functoriality on the degree-`n` tensor-power quotient: a ring homomorphism `f : R →+* S`
induces a `ℤ`-linear map
`(⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n →ₗ[ℤ] (⨂[ℤ]^n (Additive Sˣ)) ⧸ tensorRel S n`. -/
noncomputable def quotTensorPowerMap {R : Type u} [CommSemiring R] {S : Type w} [CommSemiring S]
    (f : R →+* S) (n : ℕ) :
    ((⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n) →ₗ[ℤ]
      ((⨂[ℤ]^n (Additive Sˣ)) ⧸ tensorRel S n) :=
  Submodule.mapQ (tensorRel R n) (tensorRel S n)
    (PiTensorProduct.map fun _ : Fin n ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap)
    (Submodule.map_le_iff_le_comap.mp (map_tensorRel_le f n))

/-- Evaluating `quotTensorPowerMap f n` on `Submodule.Quotient.mk w` applies
`PiTensorProduct.map` entrywise. -/
theorem quotTensorPowerMap_mk {R : Type u} [CommSemiring R] {S : Type w} [CommSemiring S]
    (f : R →+* S) {n : ℕ} (w : ⨂[ℤ]^n (Additive Rˣ)) :
    quotTensorPowerMap f n (Submodule.Quotient.mk w) = Submodule.Quotient.mk
      (PiTensorProduct.map (fun _ : Fin n ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap)
        w) :=
  Submodule.mapQ_apply _ _ _ w

/-- `quotTensorPowerMap f n` sends the quotient class of a pure tensor of units to the pure
tensor of mapped units. -/
@[simp]
theorem quotTensorPowerMap_mk_tprod {R : Type u} [CommSemiring R] {S : Type w} [CommSemiring S]
    (f : R →+* S) {n : ℕ} (a : Fin n → Rˣ) :
    quotTensorPowerMap f n (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ a))) =
      Submodule.Quotient.mk
        (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ (Units.map f.toMonoidHom ∘ a))) := by
  rw [quotTensorPowerMap_mk, PiTensorProduct.map_tprod]
  simp only [Function.comp_def, AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive,
    toMul_ofMul]

/-- The identity ring homomorphism induces the identity on
`(⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n`. -/
@[simp]
theorem quotTensorPowerMap_id (R : Type u) [CommSemiring R] (n : ℕ) :
    quotTensorPowerMap (RingHom.id R) n = LinearMap.id := by
  refine LinearMap.ext fun x ↦ Submodule.Quotient.induction_on _ x fun w ↦ ?_
  simp only [quotTensorPowerMap_mk, RingHom.toMonoidHom_eq_coe, RingHom.toMonoidHom_id,
    Units.map_id, MonoidHom.toAdditive_id, AddMonoidHom.toIntLinearMap_id,
    PiTensorProduct.map_id, LinearMap.id_apply]

/-- `quotTensorPowerMap` respects composition of ring homomorphisms. -/
theorem quotTensorPowerMap_comp {R : Type u} [CommSemiring R] {S : Type v} {T : Type w}
    [CommSemiring S] [CommSemiring T] (g : S →+* T) (f : R →+* S) (n : ℕ) :
    quotTensorPowerMap (g.comp f) n = (quotTensorPowerMap g n).comp (quotTensorPowerMap f n) := by
  refine LinearMap.ext fun x ↦ Submodule.Quotient.induction_on _ x fun w ↦ ?_
  have hcomp : (Units.map (g.comp f).toMonoidHom).toAdditive =
      (Units.map g.toMonoidHom).toAdditive.comp (Units.map f.toMonoidHom).toAdditive := by
    rw [RingHom.toMonoidHom_comp, Units.map_comp]
    exact AddMonoidHom.ext fun _ ↦ by simp
  simp only [quotTensorPowerMap_mk, LinearMap.comp_apply, hcomp, AddMonoidHom.toIntLinearMap_comp,
    PiTensorProduct.map_comp]

/-- Naturality of `degreeEquivQuotTensorPower` in arbitrary degree `n`: for any ring
homomorphism `f : R →+* S`, the degree-`n` restriction of `MilnorK.map f` corresponds to
`quotTensorPowerMap f n`. -/
theorem degreeEquivQuotTensorPower_map {R : Type u} [CommRing R] {S : Type w} [CommRing S]
    (f : R →+* S) (n : ℕ) (x : degree R n) :
    degreeEquivQuotTensorPower S n ⟨map f x, map_mem_degree f x.property⟩ =
      quotTensorPowerMap f n (degreeEquivQuotTensorPower R n x) := by
  obtain ⟨y, rfl⟩ := (degreeEquivQuotTensorPower R n).symm.surjective x
  induction y using Submodule.Quotient.induction_on with | _ w =>
  refine (degreeEquivQuotTensorPower S n).symm.injective (Subtype.ext ?_)
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    simp only [Submodule.Quotient.mk_smul, SetLike.val_smul, map_zsmul,
      coe_degreeEquivQuotTensorPower_symm_mk, TensorPower.toTensorAlgebra_tprod,
      mk_tprod_additive, map_symbol, List.map_ofFn, quotTensorPowerMap_mk,
      PiTensorProduct.map_tprod, AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive,
      Function.comp_def, toMul_ofMul, RingHom.toMonoidHom_eq_coe]
  | add w₁ w₂ hw₁ hw₂ =>
    simp only [Submodule.Quotient.mk_add, map_add, Submodule.coe_add] at hw₁ hw₂ ⊢
    rw [hw₁, hw₂]

end TauCeti.MilnorK
