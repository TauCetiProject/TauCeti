/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.LinearAlgebra.Graded.LinearMap
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Tactic.Abel
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.RingTheory.GradedAlgebra.Generators
import TauCeti.RingTheory.GradedAlgebra.SignedDerivation.Basic

/-!
# Generator criteria for signed Leibniz maps

Let `A` be an internally `ι`-graded `R`-algebra with grading `𝒜 : ι → Submodule R A`. A linear
map `d : A →ₗ[R] B` satisfies an `s`-signed Leibniz rule along `f : A → B` (for a sign function
`s : ι → ℤˣ`) when

`d (a * b) = d a * f b + s i • (f a * d b)` for `a ∈ 𝒜 i`.

Building on `TauCeti.RingTheory.GradedAlgebra.SignedDerivation.Basic`, this file develops
generator-based uniqueness, intertwining, homogeneity, and square-zero criteria for arbitrary
grading index types `ι` (in particular both `ℤ` and `ZMod 2`) and arbitrary sign maps
`s : ι → ℤˣ`:

* an `s`-signed Leibniz map along a unit-preserving map `f` is determined on any algebra-generating
  set, so two `s`-signed Leibniz endomorphisms (or an intertwining along a grading-preserving
  algebra map) are determined on any algebra-generating set;
* if `d` shifts the degrees of homogeneous generators by `q`, then `d` is homogeneous of degree `q`
  on all of `A`;
* if `d` is homogeneous of degree `q` and `s (i + q) = -s i`, then `d ∘ₗ d` is an unsigned
  derivation (`TauCeti.map_map_mul_of_leibniz`), hence vanishes on `A` as soon as it vanishes on an
  algebra-generating set.

## Main results

* `TauCeti.eq_zero_of_signedLeibniz_along_of_adjoin_eq_top`,
  `TauCeti.eq_of_signedLeibniz_along_of_adjoin_eq_top`,
  `TauCeti.eq_zero_of_signedLeibniz_of_adjoin_eq_top`,
  `TauCeti.apply_map_eq_map_apply_of_signedLeibniz_of_adjoin_eq_top`,
  `TauCeti.apply_map_eq_map_apply_of_signedLeibniz_of_adjoin_range_eq_top`,
  `TauCeti.eq_of_signedLeibniz_of_adjoin_eq_top`, and
  `TauCeti.eq_of_signedLeibniz_of_adjoin_range_eq_top`: an `s`-signed Leibniz map (along a
  unit-preserving map, as an endomorphism, or intertwined along a grading-preserving algebra map)
  is determined on any algebra-generating set.
* `TauCeti.isHomogeneous_of_signedLeibniz_of_adjoin_eq_top` and
  `TauCeti.isHomogeneous_of_signedLeibniz_of_adjoin_range_eq_top`: degree shift on generators
  propagates to the whole graded algebra.
* `TauCeti.comp_self_eq_zero_iff_of_signedLeibniz_of_adjoin_eq_top` and
  `TauCeti.comp_self_eq_zero_iff_of_signedLeibniz_of_adjoin_range_eq_top`: an odd-sign Leibniz
  endomorphism squares to zero if and only if its square vanishes on generators.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the left-factor
  graded Leibniz convention.
-/

public section

namespace TauCeti

section UniquenessAlong

variable {R A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [DecidableEq ι] [Zero ι] {𝒜 : ι → Submodule R A} [SetLike.GradedOne 𝒜]
  [DirectSum.Decomposition 𝒜] {s : ι → ℤˣ}

/-- A linear map `D : A →ₗ[R] B` satisfying an `s`-signed Leibniz rule along a unit-preserving map
`f` vanishes if it vanishes on an algebra-generating set. -/
theorem eq_zero_of_signedLeibniz_along_of_adjoin_eq_top
    {B F : Type*} [NonAssocRing B] [Module R B] [FunLike F A B] [OneHomClass F A B]
    (f : F) {D : A →ₗ[R] B}
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, D (a * b) = D a * f b + s i • (f a * D b))
    {S : Set A} (hadj : Algebra.adjoin R S = ⊤) (hS : ∀ x ∈ S, D x = 0) : D = 0 := by
  have h1 : (1 : A) ∈ LinearMap.ker D :=
    LinearMap.mem_ker.2 (map_one_eq_zero_of_leibniz_along (𝒜 := 𝒜) f hl)
  let K : Subalgebra R A :=
    (LinearMap.ker D).toSubalgebra h1 fun a b ha hb ↦ by
      rw [LinearMap.mem_ker] at ha hb ⊢
      rw [map_mul_of_leibniz_along_of_map_eq_zero (𝒜 := 𝒜) f hl a hb, ha, zero_mul]
  have htop : (⊤ : Subalgebra R A) ≤ K :=
    hadj ▸ Algebra.adjoin_le fun x hx ↦
      Submodule.mem_toSubalgebra.2 (LinearMap.mem_ker.2 (hS x hx))
  ext a
  rw [LinearMap.zero_apply, ← LinearMap.mem_ker, ← Submodule.mem_toSubalgebra]
  exact htop Algebra.mem_top

/-- Two linear maps `d₁ d₂ : A →ₗ[R] B` satisfying the same `s`-signed Leibniz rule along a
unit-preserving map `f` are equal if they agree on an algebra-generating set. -/
theorem eq_of_signedLeibniz_along_of_adjoin_eq_top
    {B F : Type*} [NonAssocRing B] [Module R B] [FunLike F A B] [OneHomClass F A B]
    (f : F) {d₁ d₂ : A →ₗ[R] B}
    (hl₁ : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d₁ (a * b) = d₁ a * f b + s i • (f a * d₁ b))
    (hl₂ : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d₂ (a * b) = d₂ a * f b + s i • (f a * d₂ b))
    {S : Set A} (hadj : Algebra.adjoin R S = ⊤) (hS : ∀ x ∈ S, d₁ x = d₂ x) : d₁ = d₂ := by
  have hzero : d₁ - d₂ = 0 := by
    refine eq_zero_of_signedLeibniz_along_of_adjoin_eq_top (𝒜 := 𝒜) (s := s) f
      (fun {i a} ha b ↦ ?_) hadj fun x hx ↦ sub_eq_zero.2 (hS x hx)
    simp only [LinearMap.sub_apply, hl₁ ha b, hl₂ ha b, sub_mul, mul_sub,
      Units.smul_def, zsmul_sub]
    abel
  exact sub_eq_zero.1 hzero

end UniquenessAlong

section Uniqueness

variable {R A ι : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  [DecidableEq ι] [Zero ι] {𝒜 : ι → Submodule R A} [SetLike.GradedOne 𝒜]
  [DirectSum.Decomposition 𝒜] {s : ι → ℤˣ}

/-- A linear endomorphism satisfying an `s`-signed Leibniz rule vanishes if it vanishes on an
algebra-generating set. -/
theorem eq_zero_of_signedLeibniz_of_adjoin_eq_top {D : A →ₗ[R] A}
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, D (a * b) = D a * b + s i • (a * D b))
    {S : Set A} (hadj : Algebra.adjoin R S = ⊤) (hS : ∀ x ∈ S, D x = 0) : D = 0 :=
  eq_zero_of_signedLeibniz_along_of_adjoin_eq_top (𝒜 := 𝒜) (OneHom.id A) hl hadj hS

/-- A grading-preserving algebra homomorphism out of `A` intertwines `s`-signed Leibniz
endomorphisms if it does so on an algebra-generating set. Neither degree-shift nor square-zero
hypotheses are needed. -/
theorem apply_map_eq_map_apply_of_signedLeibniz_of_adjoin_eq_top
    {B F : Type*} [Ring B] [Algebra R B] {ℬ : ι → Submodule R B}
    [FunLike F A B] [AlgHomClass F R A B]
    {dA : A →ₗ[R] A}
    (hdA : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, dA (a * b) = dA a * b + s i • (a * dA b))
    {dB : B →ₗ[R] B}
    (hdB : ∀ {i : ι} {b : B}, b ∈ ℬ i → ∀ c : B, dB (b * c) = dB b * c + s i • (b * dB c))
    (f : F) (hf : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → f a ∈ ℬ i)
    {S : Set A} (hadj : Algebra.adjoin R S = ⊤) (hS : ∀ x ∈ S, dB (f x) = f (dA x))
    (a : A) : dB (f a) = f (dA a) := by
  have h : dB ∘ₗ (f : A →ₗ[R] B) = (f : A →ₗ[R] B) ∘ₗ dA := by
    refine eq_of_signedLeibniz_along_of_adjoin_eq_top (𝒜 := 𝒜) (s := s) f
      (fun {i a} ha b ↦ ?_) (fun {i a} ha b ↦ ?_) hadj hS
    · simp only [LinearMap.comp_apply, LinearMap.coe_ofClass, map_mul, hdB (hf ha)]
    · simp only [LinearMap.comp_apply, LinearMap.coe_ofClass, hdA ha, map_add, map_mul,
        Units.smul_def, map_zsmul]
  exact LinearMap.congr_fun h a

/-- A grading-preserving algebra homomorphism out of `A` intertwines `s`-signed Leibniz
endomorphisms if it does so on the range of an algebra-generating map. -/
theorem apply_map_eq_map_apply_of_signedLeibniz_of_adjoin_range_eq_top
    {V B F : Type*} [Ring B] [Algebra R B] {ℬ : ι → Submodule R B}
    [FunLike F A B] [AlgHomClass F R A B]
    {dA : A →ₗ[R] A}
    (hdA : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, dA (a * b) = dA a * b + s i • (a * dA b))
    {dB : B →ₗ[R] B}
    (hdB : ∀ {i : ι} {b : B}, b ∈ ℬ i → ∀ c : B, dB (b * c) = dB b * c + s i • (b * dB c))
    (f : F) (hf : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → f a ∈ ℬ i)
    {g : V → A} (hadj : Algebra.adjoin R (Set.range g) = ⊤)
    (hg : ∀ x, dB (f (g x)) = f (dA (g x))) (a : A) : dB (f a) = f (dA a) :=
  apply_map_eq_map_apply_of_signedLeibniz_of_adjoin_eq_top (𝒜 := 𝒜) (ℬ := ℬ) hdA hdB f hf hadj
    (Set.forall_mem_range.2 hg) a

/-- Two linear endomorphisms satisfying the same `s`-signed Leibniz rule and agreeing on an
algebra-generating set are equal. -/
theorem eq_of_signedLeibniz_of_adjoin_eq_top {d₁ d₂ : A →ₗ[R] A}
    (hl₁ : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d₁ (a * b) = d₁ a * b + s i • (a * d₁ b))
    (hl₂ : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d₂ (a * b) = d₂ a * b + s i • (a * d₂ b))
    {S : Set A} (hadj : Algebra.adjoin R S = ⊤) (hS : ∀ x ∈ S, d₁ x = d₂ x) : d₁ = d₂ :=
  eq_of_signedLeibniz_along_of_adjoin_eq_top (𝒜 := 𝒜) (OneHom.id A) hl₁ hl₂ hadj hS

/-- Two `s`-signed Leibniz endomorphisms agreeing on the range of an algebra-generating map are
equal. -/
theorem eq_of_signedLeibniz_of_adjoin_range_eq_top {V : Type*} {d₁ d₂ : A →ₗ[R] A}
    (hl₁ : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d₁ (a * b) = d₁ a * b + s i • (a * d₁ b))
    (hl₂ : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d₂ (a * b) = d₂ a * b + s i • (a * d₂ b))
    {g : V → A} (hadj : Algebra.adjoin R (Set.range g) = ⊤)
    (hg : ∀ x, d₁ (g x) = d₂ (g x)) : d₁ = d₂ :=
  eq_of_signedLeibniz_of_adjoin_eq_top (𝒜 := 𝒜) hl₁ hl₂ hadj <| Set.forall_mem_range.2 hg

end Uniqueness

section Homogeneity

variable {R A ι : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  [DecidableEq ι] [AddCommMonoid ι] {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
  {s : ι → ℤˣ} {q : ι} {d : A →ₗ[R] A}

/-- An `s`-signed Leibniz endomorphism is homogeneous of degree `q` if an algebra-generating set
lies in the sum of the subspaces `𝒜 i ⊓ d⁻¹(𝒜 (i + q))`. -/
theorem isHomogeneous_of_signedLeibniz_of_adjoin_eq_top
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    {S : Set A} (hadj : Algebra.adjoin R S = ⊤)
    (hS : S ⊆ (⨆ i : ι, 𝒜 i ⊓ (𝒜 (i + q)).comap d : Submodule R A)) :
    LinearMap.IsHomogeneous d 𝒜 𝒜 q :=
  LinearMap.isHomogeneous_def.2 fun k a ha ↦
    GradedAlgebra.grade_le_of_adjoin_eq_top 𝒜
      (ℬ := fun i ↦ (𝒜 (i + q)).comap d)
      (Submodule.mem_comap.2 <| by
        rw [map_one_eq_zero_of_leibniz 𝒜 hl]
        exact zero_mem _)
      (fun {i j a b} ha hda hb hdb ↦ Submodule.mem_comap.2 <| by
        rw [hl ha b]
        have hda_b : d a * b ∈ 𝒜 ((i + j) + q) :=
          add_right_comm i q j ▸ SetLike.GradedMul.mul_mem hda hb
        have ha_db : a * d b ∈ 𝒜 ((i + j) + q) :=
          add_assoc i j q ▸ SetLike.GradedMul.mul_mem ha hdb
        refine add_mem hda_b ?_
        rw [Units.smul_def]
        exact DirectSum.Decomposition.zsmul_mem ha_db _)
      hadj hS k ha

/-- If `g : V →ₗ[R] A` is homogeneous of degree `0`, its image generates `A`, `𝒱` spans `V`, and
`d ∘ₗ g` is homogeneous of degree `q`, then any `s`-signed Leibniz endomorphism `d` is homogeneous
of degree `q`. -/
theorem isHomogeneous_of_signedLeibniz_of_adjoin_range_eq_top
    {V : Type*} [AddCommMonoid V] [Module R V] {𝒱 : ι → Submodule R V}
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    {g : V →ₗ[R] A} (hadj : Algebra.adjoin R (Set.range g) = ⊤) (h𝒱 : ⨆ i, 𝒱 i = ⊤)
    (hg : LinearMap.IsHomogeneous g 𝒱 𝒜 0) (hdg : LinearMap.IsHomogeneous (d ∘ₗ g) 𝒱 𝒜 q) :
    LinearMap.IsHomogeneous d 𝒜 𝒜 q := by
  refine isHomogeneous_of_signedLeibniz_of_adjoin_eq_top (𝒜 := 𝒜) hl hadj ?_
  rintro _ ⟨v, rfl⟩
  have hle : (⊤ : Submodule R V) ≤
      (⨆ i : ι, 𝒜 i ⊓ (𝒜 (i + q)).comap d).comap g := by
    rw [← h𝒱]
    refine iSup_le fun i x hx ↦
      le_iSup (fun k ↦ 𝒜 k ⊓ (𝒜 (k + q)).comap d) i ⟨by simpa using hg.map_mem hx, hdg.map_mem hx⟩
  exact hle Submodule.mem_top

end Homogeneity

section SquareZero

variable {R A ι : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  [DecidableEq ι] [AddMonoid ι] {𝒜 : ι → Submodule R A} [SetLike.GradedOne 𝒜]
  [DirectSum.Decomposition 𝒜] {s : ι → ℤˣ} {q : ι} {d : A →ₗ[R] A}

/-- A degree-`q` endomorphism satisfying an `s`-signed Leibniz rule with `s (i + q) = -s i` squares
to zero if and only if its square vanishes on an algebra-generating set. -/
theorem comp_self_eq_zero_iff_of_signedLeibniz_of_adjoin_eq_top
    (hdeg : LinearMap.IsHomogeneous d 𝒜 𝒜 q)
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    (hs : ∀ i, s (i + q) = -s i) {S : Set A} (hadj : Algebra.adjoin R S = ⊤) :
    d ∘ₗ d = 0 ↔ ∀ x ∈ S, d (d x) = 0 := by
  refine ⟨fun h x _ ↦ LinearMap.congr_fun h x, fun hS ↦ ?_⟩
  exact eq_zero_of_signedLeibniz_of_adjoin_eq_top (𝒜 := 𝒜) (s := fun _ ↦ 1)
    (fun {_ a} _ b ↦ by simp [map_map_mul_of_leibniz 𝒜 (fun hx ↦ hdeg.map_mem hx) hl hs a b])
    hadj hS

/-- A degree-`q` endomorphism satisfying an `s`-signed Leibniz rule with `s (i + q) = -s i` squares
to zero if and only if its square vanishes on the range of an algebra-generating map. -/
theorem comp_self_eq_zero_iff_of_signedLeibniz_of_adjoin_range_eq_top {V : Type*}
    (hdeg : LinearMap.IsHomogeneous d 𝒜 𝒜 q)
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    (hs : ∀ i, s (i + q) = -s i) {g : V → A} (hadj : Algebra.adjoin R (Set.range g) = ⊤) :
    d ∘ₗ d = 0 ↔ ∀ x, d (d (g x)) = 0 := by
  rw [comp_self_eq_zero_iff_of_signedLeibniz_of_adjoin_eq_top hdeg hl hs hadj,
    Set.forall_mem_range]

end SquareZero

end TauCeti
