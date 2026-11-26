/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Basic induction and presentation descent for Kähler differentials

Mathlib constructs the module of Kähler differentials `Ω[S⁄R]` together with two structural tools:
`KaehlerDifferential.span_range_derivation` (showing that exact differentials `D R S s` generate
`Ω[S⁄R]` over `S`) and `KaehlerDifferential.quotKerTotalEquiv` (identifying `Ω[S⁄R]` with the
quotient of the free `S`-module `S →₀ S` by `KaehlerDifferential.kerTotal R S`).

This file packages those two facts for downstream constructions of non-`S`-linear operators on
`Ω[S⁄R]` (such as the degree-one exterior differential `s • D t ↦ D s ∧ D t` and Lie derivatives
along derivations of `S`):

* `KaehlerDifferential.inductionOn`: `S`-linear span induction on `Ω[S⁄R]` with cases
  `D R S s`, `s • ω`, and `ω₁ + ω₂`.
* `TauCeti.KaehlerDifferential.span_image_D_eq_top_of_adjoin_eq_top`: the differentials of a set
  of `R`-algebra generators of `S` span `Ω[S⁄R]`.
* `TauCeti.KaehlerDifferential.map_eq_zero_of_mem_kerTotal`: proves an additive map on `S →₀ S`
  vanishes on `KaehlerDifferential.kerTotal R S` from vanishing on its three defining relation
  families and closure under `S`-scalar multiplication on
  `ker (Finsupp.linearCombination S (D R S))`.
* `TauCeti.KaehlerDifferential.liftOfKerTotal`: descends any `k`-linear map `(S →₀ S) →ₗ[k] M`
  vanishing on `KaehlerDifferential.kerTotal R S` to a `k`-linear map `Ω[S⁄R] →ₗ[k] M`, over an
  arbitrary commutative base ring `k` with `[Algebra k S]`.
-/

public section

namespace KaehlerDifferential

/-- **Span induction on Kähler differentials**: to prove a predicate on `ω : Ω[S⁄R]`, it suffices to
verify it on exact differentials `D R S s`, and show closure under `S`-scalar multiplication and
addition. -/
@[elab_as_elim]
theorem inductionOn {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {motive : Ω[S⁄R] → Prop} (ω : Ω[S⁄R])
    (D : ∀ s : S, motive (KaehlerDifferential.D R S s))
    (smul : ∀ (s : S) (ω : Ω[S⁄R]), motive ω → motive (s • ω))
    (add : ∀ ω₁ ω₂ : Ω[S⁄R], motive ω₁ → motive ω₂ → motive (ω₁ + ω₂)) :
    motive ω := by
  refine Submodule.span_induction ?_ (by simpa using D 0) (fun _ _ _ _ ↦ add _ _)
    (fun s _ _ ↦ smul s _)
    (KaehlerDifferential.span_range_derivation R S ▸ Submodule.mem_top :
      ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)))
  rintro _ ⟨s, rfl⟩
  exact D s

end KaehlerDifferential

namespace TauCeti.KaehlerDifferential

/-- If `s` generates `S` as an `R`-algebra, then the differentials of the elements of `s` span
`Ω[S⁄R]` as an `S`-module. This extracts the argument inside the proof of Mathlib's
`KaehlerDifferential.finite`. -/
theorem span_image_D_eq_top_of_adjoin_eq_top {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {s : Set S} (hs : Algebra.adjoin R s = ⊤) :
    Submodule.span S (_root_.KaehlerDifferential.D R S '' s) = ⊤ := by
  rw [eq_top_iff, ← _root_.KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  induction (hs ▸ Algebra.mem_top : x ∈ Algebra.adjoin R s) using Algebra.adjoin_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | algebraMap r => simp
  | add x y _ _ hx hy => rw [SetLike.mem_coe, map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [SetLike.mem_coe, Derivation.leibniz]
    exact add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx)

/-- **Generator criterion for vanishing on `KaehlerDifferential.kerTotal R S`**: an additive map
`f : (S →₀ S) → M` vanishes on `KaehlerDifferential.kerTotal R S` if it annihilates the three
defining relation families (additivity, Leibniz rule, and `R`-scalars) and preserves vanishing under
`S`-scalar multiplication on `ker (Finsupp.linearCombination S (D R S))`. -/
theorem map_eq_zero_of_mem_kerTotal {R S M F : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommMonoid M] [FunLike F (S →₀ S) M] [AddMonoidHomClass F (S →₀ S) M] (f : F)
    (hadd : ∀ x y : S,
      f (Finsupp.single x 1 + Finsupp.single y 1 - Finsupp.single (x + y) 1) = 0)
    (hmul : ∀ x y : S,
      f (Finsupp.single y x + Finsupp.single x y - Finsupp.single (x * y) 1) = 0)
    (hconst : ∀ r : R, f (Finsupp.single (algebraMap R S r) 1) = 0)
    (hsmul : ∀ (s : S) (v : S →₀ S),
      Finsupp.linearCombination S (_root_.KaehlerDifferential.D R S) v = 0 →
        f v = 0 → f (s • v) = 0)
    {v : S →₀ S} (hv : v ∈ _root_.KaehlerDifferential.kerTotal R S) : f v = 0 := by
  rw [_root_.KaehlerDifferential.kerTotal] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rcases hv with (⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨r, rfl⟩
    · exact hadd x y
    · exact hmul x y
    · exact hconst r
  | zero => exact map_zero f
  | add _ _ _ _ ih₁ ih₂ => rw [map_add, ih₁, ih₂, add_zero]
  | smul s v hv ih =>
    have hker : Finsupp.linearCombination S (_root_.KaehlerDifferential.D R S) v = 0 := by
      rwa [← LinearMap.mem_ker, _root_.KaehlerDifferential.kerTotal_eq]
    exact hsmul s v hker ih

variable {k S M : Type*} (R : Type*) [CommRing k] [CommRing R] [CommRing S]
  [Algebra k S] [Algebra R S] [AddCommGroup M] [Module k M]

/-- **Presentation descent for `Ω[S⁄R]`**: any `k`-linear map `f : (S →₀ S) →ₗ[k] M` that vanishes
on `KaehlerDifferential.kerTotal R S` descends along `Finsupp.linearCombination S (D R S)` to a
`k`-linear map `Ω[S⁄R] →ₗ[k] M`. -/
noncomputable def liftOfKerTotal (f : (S →₀ S) →ₗ[k] M)
    (hf : ∀ v ∈ _root_.KaehlerDifferential.kerTotal R S, f v = 0) : Ω[S⁄R] →ₗ[k] M :=
  (((_root_.KaehlerDifferential.kerTotal R S).restrictScalars k).liftQ f
    fun v hv ↦ hf v ((Submodule.restrictScalars_mem k _ v).mp hv)).comp
    ((Submodule.Quotient.restrictScalarsEquiv k
        (_root_.KaehlerDifferential.kerTotal R S)).symm.toLinearMap.comp
      ((_root_.KaehlerDifferential.quotKerTotalEquiv R S).symm.toLinearMap.restrictScalars k))

variable {R}

/-- Evaluating `liftOfKerTotal` on a formal `S`-linear combination of exact differentials recovers
`f`. -/
@[simp]
theorem liftOfKerTotal_linearCombination (f : (S →₀ S) →ₗ[k] M)
    (hf : ∀ v ∈ _root_.KaehlerDifferential.kerTotal R S, f v = 0) (w : S →₀ S) :
    liftOfKerTotal R f hf
        (Finsupp.linearCombination S (_root_.KaehlerDifferential.D R S) w) = f w := by
  have hw : (_root_.KaehlerDifferential.quotKerTotalEquiv R S).symm
      (Finsupp.linearCombination S (_root_.KaehlerDifferential.D R S) w) =
      Submodule.Quotient.mk w := by
    rw [_root_.KaehlerDifferential.quotKerTotalEquiv_symm_apply]
    exact congr($(_root_.KaehlerDifferential.derivationQuotKerTotal_lift_comp_linearCombination R S)
      w)
  simp only [liftOfKerTotal, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_toLinearMap, hw, Submodule.Quotient.restrictScalarsEquiv_symm_mk]
  exact Submodule.liftQ_apply _ _ w

/-- Evaluating `liftOfKerTotal` on `c • D R S s` gives `f (Finsupp.single s c)`. -/
@[simp]
theorem liftOfKerTotal_smul_D (f : (S →₀ S) →ₗ[k] M)
    (hf : ∀ v ∈ _root_.KaehlerDifferential.kerTotal R S, f v = 0) (c s : S) :
    liftOfKerTotal R f hf (c • _root_.KaehlerDifferential.D R S s) = f (Finsupp.single s c) := by
  rw [← Finsupp.linearCombination_single, liftOfKerTotal_linearCombination]

/-- Evaluating `liftOfKerTotal` on `D R S s` gives `f (Finsupp.single s 1)`. -/
@[simp]
theorem liftOfKerTotal_D (f : (S →₀ S) →ₗ[k] M)
    (hf : ∀ v ∈ _root_.KaehlerDifferential.kerTotal R S, f v = 0) (s : S) :
    liftOfKerTotal R f hf (_root_.KaehlerDifferential.D R S s) = f (Finsupp.single s 1) := by
  rw [← one_smul S (_root_.KaehlerDifferential.D R S s), liftOfKerTotal_smul_D]

/-- `liftOfKerTotal R f hf` is uniquely determined by its values on additive generators
`c • D R S s`. -/
theorem liftOfKerTotal_unique (f : (S →₀ S) →ₗ[k] M)
    (hf : ∀ v ∈ _root_.KaehlerDifferential.kerTotal R S, f v = 0)
    {g : Ω[S⁄R] →ₗ[k] M}
    (hg : ∀ c s : S, g (c • _root_.KaehlerDifferential.D R S s) = f (Finsupp.single s c)) :
    g = liftOfKerTotal R f hf := by
  refine LinearMap.ext fun ω ↦ ?_
  obtain ⟨w, rfl⟩ := _root_.KaehlerDifferential.linearCombination_surjective R S ω
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add w₁ w₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | single s c => rw [Finsupp.linearCombination_single, hg, liftOfKerTotal_smul_D]

end TauCeti.KaehlerDifferential
