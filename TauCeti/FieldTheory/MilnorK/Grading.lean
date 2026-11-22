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
public import TauCeti.FieldTheory.MilnorK.Basic
public import TauCeti.LinearAlgebra.TensorSquare

import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.FinCases
import TauCeti.Algebra.RingQuot
import TauCeti.LinearAlgebra.TensorAlgebra.Projection
import TauCeti.LinearAlgebra.TensorPower.Basic
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
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
* `MilnorK.degreeZeroEquiv : MilnorK.degree R 0 ≃ₗ[ℤ] ℤ` (in particular, `Nontrivial (MilnorK R)`)
* `MilnorK.degreeOneEquiv : MilnorK.degree R 1 ≃ₗ[ℤ] Additive Rˣ`
* `MilnorK.degreeTwoEquiv : MilnorK.degree R 2 ≃ₗ[ℤ] SymbolGroup R`

We also provide the graded universal property `MilnorK.gradedLift` and graded functoriality
`MilnorK.gradedMap`, together with compatibility of `degreeTwoEquiv` with `SymbolGroup.map`.

## Main definitions

* `TauCeti.MilnorK.tensorRel`: the degree-`n` Steinberg relation submodule of
  `⨂[ℤ]^n (Additive Rˣ)`.
* `TauCeti.MilnorK.degreeEquivQuotTensorPower`: canonical identification
  `MilnorK.degree R n ≃ₗ[ℤ] (⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n`.
* `TauCeti.MilnorK.degreeZeroEquiv`, `TauCeti.MilnorK.degreeOneEquiv`,
  `TauCeti.MilnorK.degreeTwoEquiv`: identifications of degrees `0`, `1`, `2` with `ℤ`,
  `Additive Rˣ`, and `SymbolGroup R`.
* `TauCeti.MilnorK.gradedLift`: graded universal property for maps into any `ℕ`-graded ring.
* `TauCeti.MilnorK.gradedMap`: graded ring homomorphism induced by a ring homomorphism `R →+* S`.

## Main results

* `TauCeti.MilnorK.isHomogeneous_ker_mkRingHom`: the Steinberg two-sided ideal is homogeneous.
* `TauCeti.MilnorK.isInternal_degree`: `MilnorK R` is the internal direct sum of `MilnorK.degree R`.
* `TauCeti.MilnorK.ker_mkRingHom_comp_toTensorAlgebra`: the kernel in degree `n` equals
  `MilnorK.tensorRel R n`.
* `TauCeti.MilnorK.tensorRel_eq_iSup`: `tensorRel R n` is the sum over `i + 2 + j = n` of
  concatenated products `T_i · R_2 · T_j`.
* `TauCeti.MilnorK.degreeTwoEquiv_map`: naturality of `degreeTwoEquiv` with respect to field and
  ring homomorphisms.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Ch. III, §7.1.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti.MilnorK

universe u v w

variable {R : Type u} [CommSemiring R]

/-! ### Homogeneity and the internal `ℕ`-grading -/

/-- The kernel of the quotient map `TensorAlgebra ℤ (Additive Rˣ) →+* MilnorK R` is homogeneous
for Mathlib's word-length grading on the tensor algebra. -/
theorem isHomogeneous_ker_mkRingHom (R : Type u) [CommSemiring R] :
    (RingHom.ker (RingQuot.mkRingHom (milnorRel R))).IsHomogeneous
      (fun n : ℕ ↦ (TensorAlgebra.ι ℤ :
        Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n) := by
  rw [← RingQuot.mkAlgHom_coe ℤ (milnorRel R)]
  refine RingQuot.isHomogeneous_ker_mkAlgHom
    (fun n : ℕ ↦ (TensorAlgebra.ι ℤ :
      Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n)
    (milnorRel R) ?_
  intro x y hxy
  rw [milnorRel_iff] at hxy
  rcases hxy with ⟨a, b, _, rfl, rfl⟩
  refine ⟨2, ?_⟩
  dsimp only
  rw [sub_zero, pow_two]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

/-- The degree submodules `MilnorK.degree R n` form an internal direct sum decomposition of
`MilnorK R`. -/
theorem isInternal_degree (R : Type u) [CommSemiring R] :
    DirectSum.IsInternal (degree R) := by
  have hdeg : degree R = fun n ↦
      Submodule.map (RingQuot.mkRingHom (milnorRel R)).toIntAlgHom.toLinearMap
        ((TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n) :=
    funext fun _ ↦ Submodule.ext fun _ ↦ mem_degree_iff
  rw [hdeg]
  exact TauCeti.GradedAlgebra.isInternal_map
    (fun n : ℕ ↦ (TensorAlgebra.ι ℤ :
      Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n)
    (RingQuot.mkRingHom (milnorRel R)).toIntAlgHom
    (RingQuot.mkRingHom_surjective (milnorRel R))
    (isHomogeneous_ker_mkRingHom R)

/-- Multiplication in `MilnorK R` is graded with respect to `MilnorK.degree R`. -/
instance instGradedMonoidDegree (R : Type u) [CommSemiring R] :
    SetLike.GradedMonoid (degree R) where
  one_mem := one_mem_degree_zero
  mul_mem _ _ _ _ hx hy := mul_mem_degree hx hy

/-- `MilnorK R` is an `ℕ`-graded ring via `MilnorK.degree R`. -/
noncomputable instance instGradedRingDegree (R : Type u) [CommSemiring R] :
    GradedRing (degree R) :=
  { instGradedMonoidDegree R with
    toDecomposition := (isInternal_degree R).chooseDecomposition }

/-! ### Graded universal property and graded functoriality -/

/-- Two graded ring homomorphisms out of `MilnorK R` agree if they agree on every `ofUnit a`. -/
theorem gradedRingHom_ext {A : Type v} {σ : Type*} [Semiring A] [SetLike σ A]
    {𝒜 : ℕ → σ} {f g : degree R →+*ᵍ 𝒜}
    (h : ∀ a : Rˣ, f (ofUnit a) = g (ofUnit a)) : f = g :=
  GradedRingHom.toRingHom_injective (ringHom_ext h)

/-- **Graded universal property of `MilnorK R`.** An additive homomorphism `f : Additive Rˣ →+ A`
into the degree-`1` piece of an `ℕ`-graded ring whose values on complementary units multiply to
zero extends uniquely to a graded ring homomorphism `MilnorK.degree R →+*ᵍ 𝒜`. -/
def gradedLift {A : Type v} {σ : Type*} [Ring A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [SetLike.GradedMonoid 𝒜] (f : Additive Rˣ →+ A)
    (hf_deg : ∀ a : Rˣ, f (Additive.ofMul a) ∈ 𝒜 1)
    (hf_rel : ∀ a b : Rˣ, (a : R) + b = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0) :
    degree R →+*ᵍ 𝒜 where
  __ := (lift f hf_rel).toRingHom
  map_mem {n x} hx := by
    rw [degree_eq_span_symbol] at hx
    refine Submodule.span_induction (p := fun y _ ↦ lift f hf_rel y ∈ 𝒜 n) ?_
      (by simp)
      (fun _ _ _ _ hx hy ↦ by simpa using add_mem hx hy)
      (fun r _ _ hx ↦ by simpa [map_zsmul] using zsmul_mem hx r) hx
    rintro _ ⟨l, hl, rfl⟩
    clear hx
    subst hl
    induction l with
    | nil =>
      simpa only [symbol_nil, List.length_nil, map_one] using SetLike.GradedOne.one_mem (A := 𝒜)
    | cons a l ih =>
      rw [symbol_cons, map_mul, lift_ofUnit, List.length_cons, add_comm]
      exact SetLike.GradedMul.mul_mem (hf_deg a) ih

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
    (gradedLift 𝒜 f hf_deg hf_rel).toRingHom = (lift f hf_rel).toRingHom :=
  ringHom_ext fun a ↦ by
    simp only [GradedRingHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      gradedLift_ofUnit, lift_ofUnit]

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
def gradedMap {S : Type w} [CommSemiring S] (f : R →+* S) : degree R →+*ᵍ degree S where
  __ := (map f).toRingHom
  map_mem hx := map_mem_degree f hx

/-- Evaluating `MilnorK.gradedMap f` on `ofUnit a` gives `ofUnit (Units.map f a)`. -/
@[simp]
theorem gradedMap_ofUnit {S : Type w} [CommSemiring S] (f : R →+* S) (a : Rˣ) :
    gradedMap f (ofUnit a) = ofUnit (Units.map f.toMonoidHom a) :=
  map_ofUnit f a

/-- The underlying ring homomorphism of `MilnorK.gradedMap f` is that of `MilnorK.map f`. -/
@[simp]
theorem toRingHom_gradedMap {S : Type w} [CommSemiring S] (f : R →+* S) :
    (gradedMap f).toRingHom = (map f).toRingHom :=
  ringHom_ext fun a ↦ by
    simp only [GradedRingHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      gradedMap_ofUnit, map_ofUnit]

/-- Evaluating `MilnorK.gradedMap f` on a symbol maps its entries in unchanged order. -/
@[simp]
theorem gradedMap_symbol {S : Type w} [CommSemiring S] (f : R →+* S) (l : List Rˣ) :
    gradedMap f (symbol l) = symbol (l.map (Units.map f.toMonoidHom)) :=
  map_symbol f l

/-- The identity ring homomorphism induces the identity graded ring homomorphism on `MilnorK`. -/
@[simp]
theorem gradedMap_id (R : Type u) [CommSemiring R] :
    gradedMap (RingHom.id R) = GradedRingHom.id (degree R) :=
  gradedRingHom_ext fun a ↦ by simp

/-- `MilnorK.gradedMap` respects composition of ring homomorphisms. -/
theorem gradedMap_comp {S : Type v} {T : Type w} [CommSemiring S] [CommSemiring T]
    (g : S →+* T) (f : R →+* S) :
    gradedMap (g.comp f) = (gradedMap g).comp (gradedMap f) :=
  gradedRingHom_ext fun a ↦ by
    simp only [gradedMap_ofUnit, GradedRingHom.comp_apply]
    rfl

/-! ### The degree-`n` Steinberg relation submodule -/

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

/-- Right concatenation preserves the Steinberg relation submodule (`R_i · T_j ⊆ R_{i+j}`). -/
theorem gMul_mem_tensorRel_left {i j : ℕ} {u : ⨂[ℤ]^i (Additive Rˣ)} {v : ⨂[ℤ]^j (Additive Rˣ)}
    (hu : u ∈ tensorRel R i) :
    GradedMonoid.GMul.mul (A := fun m ↦ ⨂[ℤ]^m (Additive Rˣ)) u v ∈ tensorRel R (i + j) := by
  induction v using PiTensorProduct.induction_on with
  | add v₁ v₂ hv₁ hv₂ =>
    rw [TensorPower.gMul_def, TensorProduct.tmul_add, map_add]; exact add_mem hv₁ hv₂
  | smul_tprod r y =>
    rw [TensorPower.gMul_def, TensorProduct.tmul_smul, map_smul]
    refine Submodule.smul_mem _ r ?_
    rw [← TensorPower.gMul_def]
    refine Submodule.span_induction
      (p := fun w _ ↦ GradedMonoid.GMul.mul (A := fun m ↦ ⨂[ℤ]^m (Additive Rˣ)) w
        (PiTensorProduct.tprod ℤ y) ∈ tensorRel R (i + j)) ?_ (by simp [TensorPower.gMul_def])
      (fun _ _ _ _ hw₁ hw₂ ↦ by
        rw [TensorPower.gMul_def, TensorProduct.add_tmul, map_add]; exact add_mem hw₁ hw₂)
      (fun s _ _ hw ↦ by
        rw [TensorPower.gMul_def, ← TensorProduct.smul_tmul', map_smul]
        exact Submodule.smul_mem _ s hw) hu
    rintro _ ⟨x, k, hk, a, b, hab, hxk, hxk1, rfl⟩
    rw [TensorPower.tprod_mul_tprod]
    exact Submodule.subset_span ⟨Fin.append x y, k, by omega, a, b, hab,
      (Fin.append_left x y ⟨k, by omega⟩).trans hxk,
      (Fin.append_left x y ⟨k + 1, hk⟩).trans hxk1, rfl⟩

/-- Left concatenation preserves the Steinberg relation submodule (`T_i · R_j ⊆ R_{i+j}`). -/
theorem gMul_mem_tensorRel_right {i j : ℕ} {u : ⨂[ℤ]^i (Additive Rˣ)} {v : ⨂[ℤ]^j (Additive Rˣ)}
    (hv : v ∈ tensorRel R j) :
    GradedMonoid.GMul.mul (A := fun m ↦ ⨂[ℤ]^m (Additive Rˣ)) u v ∈ tensorRel R (i + j) := by
  induction u using PiTensorProduct.induction_on with
  | add u₁ u₂ hu₁ hu₂ =>
    rw [TensorPower.gMul_def, TensorProduct.add_tmul, map_add]; exact add_mem hu₁ hu₂
  | smul_tprod r x =>
    rw [TensorPower.gMul_def, ← TensorProduct.smul_tmul', map_smul]
    refine Submodule.smul_mem _ r ?_
    rw [← TensorPower.gMul_def]
    refine Submodule.span_induction
      (p := fun w _ ↦ GradedMonoid.GMul.mul (A := fun m ↦ ⨂[ℤ]^m (Additive Rˣ))
        (PiTensorProduct.tprod ℤ x) w ∈ tensorRel R (i + j)) ?_ (by simp [TensorPower.gMul_def])
      (fun _ _ _ _ hw₁ hw₂ ↦ by
        rw [TensorPower.gMul_def, TensorProduct.tmul_add, map_add]; exact add_mem hw₁ hw₂)
      (fun s _ _ hw ↦ by
        rw [TensorPower.gMul_def, TensorProduct.tmul_smul, map_smul]
        exact Submodule.smul_mem _ s hw) hv
    rintro _ ⟨y, k, hk, a, b, hab, hyk, hyk1, rfl⟩
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
      Submodule.subset_span ⟨_, 0, by decide, a, b, hab, rfl, rfl, rfl⟩,
      PiTensorProduct.tprod ℤ (fun q : Fin (n - (k + 2)) ↦ y (Fin.natAdd (k + 2) q)), ?_⟩
    rw [hmid, TensorPower.tprod_mul_tprod, TensorPower.tprod_mul_tprod,
      Fin.append_castAdd_natAdd (f := fun i ↦ y (Fin.castAdd _ i)),
      Fin.append_castAdd_natAdd (f := y), TensorPower.cast_tprod]
    rfl
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
    exact Submodule.subset_span
      ⟨![Additive.ofMul a, Additive.ofMul b], 0, by decide, a, b, hab, rfl, rfl, rfl⟩
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

/-! ### The homogeneous Steinberg quotient bridge -/

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
      have hof : ∀ {k} (w : ⨂[ℤ]^k (Additive Rˣ)),
          TensorAlgebra.ofDirectSum (DirectSum.of (fun m ↦ ⨂[ℤ]^m (Additive Rˣ)) k w) =
            TensorPower.toTensorAlgebra w := fun {k} w ↦
        DirectSum.toAddMonoid_of
          (fun _ ↦ (TensorPower.toTensorAlgebra (R := ℤ) (M := Additive Rˣ)).toAddMonoidHom) k w
      rw [hof u, hof v, hmid,
        ← TensorPower.toTensorAlgebra_gMul, ← TensorPower.toTensorAlgebra_gMul]
      have hr : PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b] ∈ tensorRel R 2 :=
        Submodule.subset_span ⟨![Additive.ofMul a, Additive.ofMul b], 0, by decide, a, b, hab,
          rfl, rfl, rfl⟩
      have hw := gMul_mem_tensorRel_left (v := v) (gMul_mem_tensorRel_right (u := u) hr)
      by_cases hdeg : i + 2 + j = n
      · subst hdeg; rw [TensorAlgebra.tensorPowerProjection_toTensorAlgebra]; exact hw
      · rw [TensorAlgebra.tensorPowerProjection_of_mem_range_pow_ne hdeg
          (TensorPower.toTensorAlgebra_mem_range_pow _ _)]; exact zero_mem _

/-- **Homogeneous kernel identification.** The kernel of the quotient map
`TensorPower ℤ n (Additive Rˣ) → TensorAlgebra ℤ (Additive Rˣ) → MilnorK R` is exactly
`MilnorK.tensorRel R n`. -/
theorem ker_mkRingHom_comp_toTensorAlgebra (R : Type u) [CommSemiring R] (n : ℕ) :
    LinearMap.ker
      ((RingQuot.mkRingHom (milnorRel R)).toIntAlgHom.toLinearMap.comp
        (TensorPower.toTensorAlgebra (R := ℤ) (M := Additive Rˣ) (n := n))) =
      tensorRel R n := by
  refine le_antisymm ?_ ?_
  · intro w hw
    have hker : TensorPower.toTensorAlgebra w ∈ RingHom.ker (RingQuot.mkRingHom (milnorRel R)) :=
      hw
    rw [RingQuot.ker_mkRingHom_eq_span] at hker
    let H : Submodule ℤ (TensorAlgebra ℤ (Additive Rˣ)) :=
      (tensorRel R n).comap (TensorAlgebra.tensorPowerProjection n)
    have hsub :
        (TwoSidedIdeal.span {z | ∃ x y, milnorRel R x y ∧ z = x - y} :
          Set (TensorAlgebra ℤ (Additive Rˣ))) ⊆ H.toAddSubgroup := by
      rw [TauCeti.TwoSidedIdeal.coe_span_subset_addSubgroup_iff]
      rintro p _ ⟨_, _, hrel, rfl⟩ q
      rw [milnorRel_iff] at hrel
      rcases hrel with ⟨a, b, hab, rfl, rfl⟩
      rw [sub_zero]
      exact tensorPowerProjection_mul_steinberg_mul_mem_tensorRel p q hab
    have hwH : TensorPower.toTensorAlgebra w ∈ H := hsub hker
    rw [Submodule.mem_comap, TensorAlgebra.tensorPowerProjection_toTensorAlgebra] at hwH
    exact hwH
  · rw [tensorRel, Submodule.span_le]
    rintro _ ⟨x, k, hk, a, b, hab, hxk, hxk1, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply,
      TensorPower.toTensorAlgebra_tprod, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_apply]
    have hx : x = Additive.ofMul ∘ (Additive.toMul ∘ x) :=
      funext fun _ ↦ (ofMul_toMul _).symm
    rw [hx, mkRingHom_tprod]
    set l : List Rˣ := List.ofFn (Additive.toMul ∘ x)
    have hlen : l.length = n := List.length_ofFn
    have hsplit : l = l.take k ++ a :: b :: l.drop (k + 2) := by
      conv_lhs =>
        rw [← List.take_append_drop k l, List.drop_eq_getElem_cons (by omega),
          List.drop_eq_getElem_cons (by omega)]
      simp [l, hxk, hxk1]
    rw [hsplit]
    exact symbol_eq_zero_of_add_eq_one _ _ hab

/-- Intersecting the Steinberg kernel with the degree-`n` piece of the tensor algebra yields the
image of `tensorRel R n`. -/
theorem ker_mkRingHom_inf_range_pow (R : Type u) [CommSemiring R] (n : ℕ) :
    LinearMap.ker (RingQuot.mkRingHom (milnorRel R)).toIntAlgHom.toLinearMap ⊓
        (TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n =
      (tensorRel R n).map (TensorPower.toTensorAlgebra (R := ℤ) (M := Additive Rˣ) (n := n)) := by
  refine Submodule.ext fun t ↦ ⟨?_, ?_⟩
  · rintro ⟨ht_ker, ht_deg⟩
    rw [← TensorPower.range_toTensorAlgebra] at ht_deg
    rcases ht_deg with ⟨w, rfl⟩
    exact ⟨w, by rw [← ker_mkRingHom_comp_toTensorAlgebra]; exact ht_ker, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨by rw [← ker_mkRingHom_comp_toTensorAlgebra] at hw; exact hw,
      TensorPower.toTensorAlgebra_mem_range_pow n w⟩

/-- The canonical linear map from `⨂[ℤ]^n (Additive Rˣ)` onto `MilnorK.degree R n`. -/
private noncomputable def tensorPowerToDegree (R : Type u) [CommSemiring R] (n : ℕ) :
    (⨂[ℤ]^n (Additive Rˣ)) →ₗ[ℤ] degree R n :=
  ((RingQuot.mkRingHom (milnorRel R)).toIntAlgHom.toLinearMap.comp
    (TensorPower.toTensorAlgebra (R := ℤ) (M := Additive Rˣ) (n := n))).codRestrict (degree R n)
    fun w ↦ mem_degree_iff.mpr
      ⟨TensorPower.toTensorAlgebra w, TensorPower.toTensorAlgebra_mem_range_pow n w, rfl⟩

private theorem tensorPowerToDegree_surjective (R : Type u) [CommSemiring R] (n : ℕ) :
    Function.Surjective (tensorPowerToDegree R n) := by
  rintro ⟨x, hx⟩
  rw [mem_degree_iff] at hx
  rcases hx with ⟨t, ht, rfl⟩
  rw [← TensorPower.range_toTensorAlgebra] at ht
  rcases ht with ⟨w, rfl⟩
  exact ⟨w, rfl⟩

private theorem ker_tensorPowerToDegree (R : Type u) [CommSemiring R] (n : ℕ) :
    LinearMap.ker (tensorPowerToDegree R n) = tensorRel R n := by
  rw [← ker_mkRingHom_comp_toTensorAlgebra R n]
  exact Submodule.ext fun _ ↦ by simp [tensorPowerToDegree]

/-- **The homogeneous Steinberg quotient bridge.** In every degree `n`, the degree-`n` Milnor
group is canonically isomorphic to `(⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n`. -/
noncomputable def degreeEquivQuotTensorPower (R : Type u) [CommSemiring R] (n : ℕ) :
    degree R n ≃ₗ[ℤ] (⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n :=
  ((Submodule.quotEquivOfEq (tensorRel R n) _ (ker_tensorPowerToDegree R n).symm).trans
    ((tensorPowerToDegree R n).quotKerEquivOfSurjective
      (tensorPowerToDegree_surjective R n))).symm

/-- The inverse of `degreeEquivQuotTensorPower` sends the class of a tensor `w` to the image
of `TensorPower.toTensorAlgebra w` in `MilnorK R`. -/
theorem coe_degreeEquivQuotTensorPower_symm_mk {n : ℕ} (w : ⨂[ℤ]^n (Additive Rˣ)) :
    ((degreeEquivQuotTensorPower R n).symm (Submodule.Quotient.mk w) : MilnorK R) =
      RingQuot.mkRingHom (milnorRel R) (TensorPower.toTensorAlgebra w) := by
  rw [degreeEquivQuotTensorPower, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- The inverse of `degreeEquivQuotTensorPower` sends the class of a pure tensor to the
corresponding Milnor symbol. -/
@[simp]
theorem coe_degreeEquivQuotTensorPower_symm_mk_tprod {n : ℕ} (a : Fin n → Rˣ) :
    ((degreeEquivQuotTensorPower R n).symm
      (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ a))) : MilnorK R) =
      symbol (List.ofFn a) := by
  rw [coe_degreeEquivQuotTensorPower_symm_mk, TensorPower.toTensorAlgebra_tprod, mkRingHom_tprod]

/-- `degreeEquivQuotTensorPower` sends a Milnor symbol to the class of its pure tensor. -/
@[simp]
theorem degreeEquivQuotTensorPower_symbol {n : ℕ} (a : Fin n → Rˣ) :
    degreeEquivQuotTensorPower R n
      ⟨symbol (List.ofFn a),
        by simpa only [List.length_ofFn] using symbol_mem_degree (List.ofFn a)⟩ =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ a)) := by
  apply (degreeEquivQuotTensorPower R n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact Subtype.ext (coe_degreeEquivQuotTensorPower_symm_mk_tprod a).symm

/-! ### Low-degree identifications: `K₀ᴹ ≃ ℤ`, `K₁ᴹ ≃ Additive Rˣ`, `K₂ᴹ ≃ SymbolGroup R` -/

/-- Canonical identification `MilnorK.degree R 0 ≃ₗ[ℤ] ℤ`. -/
noncomputable def degreeZeroEquiv (R : Type u) [CommSemiring R] : degree R 0 ≃ₗ[ℤ] ℤ :=
  (degreeEquivQuotTensorPower R 0).trans
    ((Submodule.quotEquivOfEqBot _ (tensorRel_zero R)).trans
      (PiTensorProduct.isEmptyEquiv (Fin 0)))

/-- `degreeZeroEquiv` sends the multiplicative identity `1` to `1 : ℤ`. -/
@[simp]
theorem degreeZeroEquiv_one : degreeZeroEquiv R ⟨1, one_mem_degree_zero⟩ = 1 := by
  have h1 : (⟨1, one_mem_degree_zero⟩ : degree R 0) =
      ⟨symbol (List.ofFn (Fin.elim0 : Fin 0 → Rˣ)),
        by simpa only [List.length_ofFn] using symbol_mem_degree (List.ofFn Fin.elim0)⟩ :=
    Subtype.ext (by simp)
  rw [h1, degreeZeroEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    degreeEquivQuotTensorPower_symbol]
  simp [Submodule.quotEquivOfEqBot]

/-- The inverse of `degreeZeroEquiv` sends an integer `k` to its cast `(k : MilnorK R)`. -/
@[simp]
theorem coe_degreeZeroEquiv_symm (k : ℤ) : ((degreeZeroEquiv R).symm k : MilnorK R) = k := by
  have h1 : ((degreeZeroEquiv R).symm 1 : MilnorK R) = 1 := by
    simpa only [degreeZeroEquiv_one] using congrArg Subtype.val
      ((degreeZeroEquiv R).symm_apply_apply ⟨1, one_mem_degree_zero⟩)
  conv_lhs => rw [← mul_one k, ← smul_eq_mul]
  rw [map_zsmul, Submodule.coe_smul, h1, zsmul_one]

/-- `MilnorK R` is always nontrivial: `1 ≠ 0`, witnessed by `degreeZeroEquiv : K₀ᴹ(R) ≃ ℤ`. -/
instance instNontrivial (R : Type u) [CommSemiring R] : Nontrivial (MilnorK R) :=
  nontrivial_of_ne 1 0 fun h ↦ one_ne_zero (α := ℤ) <| by
    simpa [degreeZeroEquiv_one] using
      congrArg (degreeZeroEquiv R) (Subtype.ext h : (⟨1, one_mem_degree_zero⟩ : degree R 0) = 0)

/-- Canonical identification `MilnorK.degree R 1 ≃ₗ[ℤ] Additive Rˣ`. -/
noncomputable def degreeOneEquiv (R : Type u) [CommSemiring R] : degree R 1 ≃ₗ[ℤ] Additive Rˣ :=
  (degreeEquivQuotTensorPower R 1).trans
    ((Submodule.quotEquivOfEqBot _ (tensorRel_one R)).trans
      (TauCeti.TensorPower.oneEquiv ℤ (Additive Rˣ)))

/-- `degreeOneEquiv` sends `ofUnit a` to `Additive.ofMul a`. -/
@[simp]
theorem degreeOneEquiv_ofUnit (a : Rˣ) :
    degreeOneEquiv R ⟨ofUnit a, ofUnit_mem_degree_one a⟩ = Additive.ofMul a := by
  have h1 : (⟨ofUnit a, ofUnit_mem_degree_one a⟩ : degree R 1) =
      ⟨symbol (List.ofFn (fun _ : Fin 1 ↦ a)), by
        simpa only [List.length_ofFn] using symbol_mem_degree (List.ofFn fun _ : Fin 1 ↦ a)⟩ :=
    Subtype.ext (by simp)
  rw [h1, degreeOneEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    degreeEquivQuotTensorPower_symbol]
  simp [Submodule.quotEquivOfEqBot]

/-- The inverse of `degreeOneEquiv` sends `Additive.ofMul a` to `ofUnit a`. -/
@[simp]
theorem coe_degreeOneEquiv_symm (a : Rˣ) :
    ((degreeOneEquiv R).symm (Additive.ofMul a) : MilnorK R) = ofUnit a := by
  simpa only [degreeOneEquiv_ofUnit] using congrArg Subtype.val
    ((degreeOneEquiv R).symm_apply_apply ⟨ofUnit a, ofUnit_mem_degree_one a⟩)

/-- The degree-one map `ofUnit : Rˣ → MilnorK R` is injective. -/
theorem ofUnit_injective (R : Type u) [CommSemiring R] :
    Function.Injective (ofUnit (R := R)) := fun a b h ↦
  Additive.ofMul.injective <| by
    simpa only [degreeOneEquiv_ofUnit] using congrArg (degreeOneEquiv R)
      (Subtype.ext h : (⟨ofUnit a, ofUnit_mem_degree_one a⟩ : degree R 1) =
        ⟨ofUnit b, ofUnit_mem_degree_one b⟩)

/-- Canonical identification `MilnorK.degree R 2 ≃ₗ[ℤ] SymbolGroup R`. -/
noncomputable def degreeTwoEquiv (R : Type u) [CommSemiring R] :
    degree R 2 ≃ₗ[ℤ] SymbolGroup R :=
  (degreeEquivQuotTensorPower R 2).trans
    (Submodule.Quotient.equiv (steinbergRelations R) (tensorRel R 2)
      (TauCeti.tensorProductEquivTensorSquare ℤ (Additive Rˣ))
      (map_steinbergRelations_eq_tensorRel_two R)).symm

/-- `degreeTwoEquiv` sends the product `ofUnit a * ofUnit b` to `TauCeti.symbol a b`. -/
@[simp]
theorem degreeTwoEquiv_ofUnit_mul (a b : Rˣ) :
    degreeTwoEquiv R
      ⟨ofUnit a * ofUnit b, mul_mem_degree (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩ =
      TauCeti.symbol a b := by
  have h2 : (⟨ofUnit a * ofUnit b,
      mul_mem_degree (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩ : degree R 2) =
      ⟨symbol (List.ofFn ![a, b]),
        by simpa only [List.length_ofFn] using symbol_mem_degree (List.ofFn ![a, b])⟩ :=
    Subtype.ext (by simp)
  rw [h2, degreeTwoEquiv, LinearEquiv.trans_apply, degreeEquivQuotTensorPower_symbol,
    LinearEquiv.symm_apply_eq, TauCeti.symbol_def]
  calc Submodule.Quotient.mk (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ ![a, b]))
      = Submodule.Quotient.mk (TauCeti.tensorProductEquivTensorSquare ℤ (Additive Rˣ)
          (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b)) := by
        rw [TauCeti.tensorProductEquivTensorSquare_tmul]
        exact congrArg (Submodule.Quotient.mk (p := tensorRel R 2))
          (congrArg (PiTensorProduct.tprod ℤ) (funext fun i ↦ by fin_cases i <;> rfl))
    _ = _ := ((Submodule.Quotient.equiv_apply (steinbergRelations R) (tensorRel R 2)
          (TauCeti.tensorProductEquivTensorSquare ℤ (Additive Rˣ))
          (map_steinbergRelations_eq_tensorRel_two R) _).trans
          (Submodule.mapQ_apply _ _ _ _)).symm

/-- The inverse of `degreeTwoEquiv` sends `TauCeti.symbol a b` to `ofUnit a * ofUnit b`. -/
@[simp]
theorem coe_degreeTwoEquiv_symm_symbol (a b : Rˣ) :
    ((degreeTwoEquiv R).symm (TauCeti.symbol a b) : MilnorK R) = ofUnit a * ofUnit b := by
  simpa only [degreeTwoEquiv_ofUnit_mul] using congrArg Subtype.val
    ((degreeTwoEquiv R).symm_apply_apply
      ⟨ofUnit a * ofUnit b, mul_mem_degree (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩)

/-- Naturality of `degreeTwoEquiv`: for any ring homomorphism `f : R →+* S`, the degree-`2`
restriction of `MilnorK.map f` corresponds to `SymbolGroup.map f`. -/
theorem degreeTwoEquiv_map {S : Type w} [CommSemiring S] (f : R →+* S) (x : degree R 2) :
    degreeTwoEquiv S ⟨map f x, map_mem_degree f x.property⟩ =
      SymbolGroup.map f (degreeTwoEquiv R x) := by
  apply (degreeTwoEquiv S).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext; dsimp only
  obtain ⟨y, rfl⟩ := (degreeTwoEquiv R).symm.surjective x
  rw [LinearEquiv.apply_symm_apply]
  induction y using SymbolGroup.induction_on with
  | symbol a b => simp
  | add y₁ y₂ hy₁ hy₂ => simp only [map_add, Submodule.coe_add, hy₁, hy₂]

/-! ### Arbitrary-degree naturality -/

/-- Applying a ring homomorphism entrywise on `⨂[ℤ]^n (Additive Rˣ)` preserves `tensorRel`. -/
theorem map_tensorRel_le {S : Type w} [CommSemiring S] (f : R →+* S) (n : ℕ) :
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
noncomputable def quotTensorPowerMap {S : Type w} [CommSemiring S] (f : R →+* S) (n : ℕ) :
    ((⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n) →ₗ[ℤ]
      ((⨂[ℤ]^n (Additive Sˣ)) ⧸ tensorRel S n) :=
  Submodule.mapQ (tensorRel R n) (tensorRel S n)
    (PiTensorProduct.map fun _ : Fin n ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap)
    (Submodule.map_le_iff_le_comap.mp (map_tensorRel_le f n))

/-- Evaluating `quotTensorPowerMap f n` on `Submodule.Quotient.mk w` applies
`PiTensorProduct.map` entrywise. -/
theorem quotTensorPowerMap_mk {S : Type w} [CommSemiring S] (f : R →+* S) {n : ℕ}
    (w : ⨂[ℤ]^n (Additive Rˣ)) :
    quotTensorPowerMap f n (Submodule.Quotient.mk w) = Submodule.Quotient.mk
      (PiTensorProduct.map (fun _ : Fin n ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap)
        w) :=
  Submodule.mapQ_apply _ _ _ w

/-- `quotTensorPowerMap f n` sends the quotient class of a pure tensor of units to the pure
tensor of mapped units. -/
@[simp]
theorem quotTensorPowerMap_mk_tprod {S : Type w} [CommSemiring S] (f : R →+* S) {n : ℕ}
    (a : Fin n → Rˣ) :
    quotTensorPowerMap f n (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ a))) =
      Submodule.Quotient.mk
        (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ (Units.map f.toMonoidHom ∘ a))) := by
  rw [quotTensorPowerMap_mk, PiTensorProduct.map_tprod]; rfl

/-- The identity ring homomorphism induces the identity on
`(⨂[ℤ]^n (Additive Rˣ)) ⧸ tensorRel R n`. -/
@[simp]
theorem quotTensorPowerMap_id (R : Type u) [CommSemiring R] (n : ℕ) :
    quotTensorPowerMap (RingHom.id R) n = LinearMap.id := by
  refine LinearMap.ext fun x ↦ Submodule.Quotient.induction_on _ x fun w ↦ ?_
  have hid : (fun _ : Fin n ↦ (Units.map (RingHom.id R).toMonoidHom).toAdditive.toIntLinearMap) =
      fun _ ↦ LinearMap.id := funext fun _ ↦ LinearMap.ext fun _ ↦ rfl
  rw [quotTensorPowerMap_mk, hid, PiTensorProduct.map_id, LinearMap.id_apply, LinearMap.id_apply]

/-- `quotTensorPowerMap` respects composition of ring homomorphisms. -/
theorem quotTensorPowerMap_comp {S : Type v} {T : Type w} [CommSemiring S] [CommSemiring T]
    (g : S →+* T) (f : R →+* S) (n : ℕ) :
    quotTensorPowerMap (g.comp f) n = (quotTensorPowerMap g n).comp (quotTensorPowerMap f n) := by
  refine LinearMap.ext fun x ↦ Submodule.Quotient.induction_on _ x fun w ↦ ?_
  have hcomp : (fun _ : Fin n ↦ (Units.map (g.comp f).toMonoidHom).toAdditive.toIntLinearMap) =
      fun _ ↦ (Units.map g.toMonoidHom).toAdditive.toIntLinearMap ∘ₗ
        (Units.map f.toMonoidHom).toAdditive.toIntLinearMap :=
    funext fun _ ↦ LinearMap.ext fun _ ↦ rfl
  simp only [quotTensorPowerMap_mk, LinearMap.comp_apply, hcomp, PiTensorProduct.map_comp]

/-- Naturality of `degreeEquivQuotTensorPower` in arbitrary degree `n`: for any ring
homomorphism `f : R →+* S`, the degree-`n` restriction of `MilnorK.map f` corresponds to
`quotTensorPowerMap f n`. -/
theorem degreeEquivQuotTensorPower_map {S : Type w} [CommSemiring S] (f : R →+* S) (n : ℕ)
    (x : degree R n) :
    degreeEquivQuotTensorPower S n ⟨map f x, map_mem_degree f x.property⟩ =
      quotTensorPowerMap f n (degreeEquivQuotTensorPower R n x) := by
  apply (degreeEquivQuotTensorPower S n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext; dsimp only
  obtain ⟨y, rfl⟩ := (degreeEquivQuotTensorPower R n).symm.surjective x
  rw [LinearEquiv.apply_symm_apply]
  induction y using Submodule.Quotient.induction_on with | _ w =>
  rw [coe_degreeEquivQuotTensorPower_symm_mk, quotTensorPowerMap_mk,
    coe_degreeEquivQuotTensorPower_symm_mk]
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    let u : Fin n → Rˣ := Additive.toMul ∘ a
    have ha : PiTensorProduct.tprod ℤ a = PiTensorProduct.tprod ℤ (Additive.ofMul ∘ u) := rfl
    have hmap : PiTensorProduct.map
        (fun _ : Fin n ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap)
        (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ u)) =
        PiTensorProduct.tprod ℤ (Additive.ofMul ∘ (Units.map f.toMonoidHom ∘ u)) :=
      PiTensorProduct.map_tprod _ _
    simp only [ha, map_smul, hmap, TensorPower.toTensorAlgebra_tprod, map_zsmul, mkRingHom_tprod,
      map_symbol, List.map_ofFn]
  | add w₁ w₂ hw₁ hw₂ => simp only [map_add, hw₁, hw₂]

end TauCeti.MilnorK
