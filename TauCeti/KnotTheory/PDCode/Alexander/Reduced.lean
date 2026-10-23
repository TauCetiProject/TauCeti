/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Alexander.Basic
public import Mathlib.Algebra.Exact.Basic
import Mathlib.RingTheory.Localization.Submodule

/-!
# Removing the free summand of a diagram's Alexander module

The augmentation sends every Wirtinger generator to `1`. Its kernel is independent of a
base arc; choosing a generator splits the Alexander module as this kernel times the Laurent
polynomial ring. The differences from that generator span the kernel and satisfy the same
homogeneous crossing relations, with the chosen generator set to zero.

The first elementary ideal is the zeroth Fitting ideal of the augmentation kernel, including
for the empty diagram. This removes the free summand before computing an Alexander
polynomial from a reduced presentation. No principality or normalization of that ideal is
asserted here, and the construction applies to links as well as knots.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Graduate Texts in Mathematics 57,
  Springer (1977), Chapters VI–VII (augmentation and the Alexander matrix).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Graduate Texts in Mathematics 175,
  Springer (1997), Chapter 6.

The augmentation uses `OrientedPDCode.alexanderLift`. The splitting uses Mathlib's
`Function.Exact.splitSurjectiveEquiv`, and the Fitting-ideal shift uses
`TauCeti.fittingIdeal_prod_add_finrank`.
-/

public section

noncomputable section

open LaurentPolynomial Submodule

namespace TauCeti.OrientedPDCode

variable {n : ℕ} (D : OrientedPDCode n)

/-- The augmentation kernel, with no choice of base generator. -/
abbrev ReducedAlexanderModule := LinearMap.ker D.alexanderAugmentation

variable (g₀ : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount)

/-- Projection to the augmentation kernel, obtained by subtracting the augmentation times
the chosen generator. -/
def alexanderReduction : D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] D.ReducedAlexanderModule :=
  (LinearMap.id - (LinearMap.toSpanSingleton ℤ[T;T⁻¹] D.AlexanderModule
    (D.alexanderGenerator g₀)).comp D.alexanderAugmentation).codRestrict _
      (fun x => by simp)

/-- The projection subtracts the free component along the chosen generator. -/
@[simp]
theorem coe_alexanderReduction (x : D.AlexanderModule) :
    (D.alexanderReduction g₀ x : D.AlexanderModule) =
      x - D.alexanderAugmentation x • D.alexanderGenerator g₀ := (rfl)

/-- The projection fixes the augmentation kernel. -/
@[simp]
theorem alexanderReduction_coe (x : D.ReducedAlexanderModule) :
    D.alexanderReduction g₀ x = x := by
  apply Subtype.ext
  simp [LinearMap.mem_ker.mp x.2]

/-- Projection onto the reduced Alexander module is surjective. -/
theorem alexanderReduction_surjective : Function.Surjective (D.alexanderReduction g₀) :=
  fun x => ⟨x, D.alexanderReduction_coe g₀ x⟩

/-- The difference of a generator from the chosen generator, in the augmentation kernel. -/
def reducedAlexanderGenerator
    (g : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) : D.ReducedAlexanderModule :=
  D.alexanderReduction g₀ (D.alexanderGenerator g)

/-- A reduced generator is the corresponding difference in the original module. -/
@[simp]
theorem coe_reducedAlexanderGenerator
    (g : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) :
    (D.reducedAlexanderGenerator g₀ g : D.AlexanderModule) =
      D.alexanderGenerator g - D.alexanderGenerator g₀ := by
  simp [reducedAlexanderGenerator]

/-- The chosen reduced generator vanishes. -/
@[simp]
theorem reducedAlexanderGenerator_self : D.reducedAlexanderGenerator g₀ g₀ = 0 := by
  apply Subtype.ext
  simp

/-- The generator differences span the augmentation kernel. -/
theorem span_range_reducedAlexanderGenerator :
    span ℤ[T;T⁻¹] (Set.range (D.reducedAlexanderGenerator g₀)) = ⊤ := by
  have hgen : D.reducedAlexanderGenerator g₀ =
      D.alexanderReduction g₀ ∘ D.alexanderGenerator := rfl
  rw [hgen, Set.range_comp, ← Submodule.map_span,
    D.span_range_alexanderGenerator, Submodule.map_top,
    LinearMap.range_eq_top.mpr (D.alexanderReduction_surjective g₀)]

/-- The reduced Alexander module is finitely generated, even for an empty diagram. -/
instance : Module.Finite ℤ[T;T⁻¹] D.ReducedAlexanderModule := by
  have : IsNoetherianRing ℤ[T;T⁻¹] :=
    IsLocalization.isNoetherianRing (Submonoid.powers (Polynomial.X : Polynomial ℤ))
      ℤ[T;T⁻¹] inferInstance
  infer_instance

/-- The two half-edges of an arc give the same reduced generator. -/
@[simp]
theorem reducedAlexanderGenerator_edgePair (h : Fin (4 * n)) :
    D.reducedAlexanderGenerator g₀ (.inl (D.edgePair.val h)) =
      D.reducedAlexanderGenerator g₀ (.inl h) := by
  simp [reducedAlexanderGenerator]

/-- Reduced generators satisfy the homogeneous Alexander crossing relation. -/
theorem reducedAlexanderGenerator_crossing_add_two (i : Fin n) (slot : Fin 4) :
    D.reducedAlexanderGenerator g₀ (.inl (D.crossing i (slot + 2))) =
      D.alexanderWeight i slot • D.reducedAlexanderGenerator g₀ (.inl (D.crossing i slot)) +
        (1 - D.alexanderWeight i slot) •
          D.reducedAlexanderGenerator g₀ (.inl (D.crossing i (slot + 1))) := by
  simp only [reducedAlexanderGenerator, D.alexanderGenerator_crossing_add_two,
    map_add, map_smul]

/-- Linear maps from the reduced module are determined by the generator differences. -/
@[ext]
theorem ReducedAlexanderModule.hom_ext {M : Type*} [AddCommGroup M] [Module ℤ[T;T⁻¹] M]
    {f g : D.ReducedAlexanderModule →ₗ[ℤ[T;T⁻¹]] M}
    (h : ∀ x, f (D.reducedAlexanderGenerator g₀ x) = g (D.reducedAlexanderGenerator g₀ x)) :
    f = g :=
  LinearMap.ext_on_range (D.span_range_reducedAlexanderGenerator g₀) h

/-- Prescribing generator differences satisfying the arc and crossing relations, with zero
at the chosen generator, determines a unique linear map from the augmentation kernel. -/
theorem existsUnique_reducedAlexanderLift {M : Type*} [AddCommGroup M]
    [Module ℤ[T;T⁻¹] M]
    (v : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount → M)
    (harc : ∀ h, v (.inl (D.edgePair.val h)) = v (.inl h))
    (hcross : ∀ i slot, v (.inl (D.crossing i (slot + 2))) =
      D.alexanderWeight i slot • v (.inl (D.crossing i slot)) +
        (1 - D.alexanderWeight i slot) • v (.inl (D.crossing i (slot + 1))))
    (hbase : v g₀ = 0) :
    ∃! f : D.ReducedAlexanderModule →ₗ[ℤ[T;T⁻¹]] M,
      ∀ g, f (D.reducedAlexanderGenerator g₀ g) = v g := by
  refine ⟨(D.alexanderLift v harc hcross).comp D.ReducedAlexanderModule.subtype, ?_, ?_⟩
  · intro g
    simp [hbase]
  · intro f hf
    apply ReducedAlexanderModule.hom_ext D g₀
    intro g
    simp [hf, hbase]

/-- The augmentation sequence splits at any chosen diagram generator. -/
def alexanderSplitting : D.AlexanderModule ≃ₗ[ℤ[T;T⁻¹]]
    D.ReducedAlexanderModule × ℤ[T;T⁻¹] :=
  ((LinearMap.exact_subtype_ker_map D.alexanderAugmentation).splitSurjectiveEquiv
    (Submodule.injective_subtype _)
    ⟨LinearMap.toSpanSingleton ℤ[T;T⁻¹] D.AlexanderModule (D.alexanderGenerator g₀),
      by ext; simp⟩).1

/-- The scalar component of the splitting is the augmentation. -/
@[simp]
theorem alexanderSplitting_snd (x : D.AlexanderModule) :
    (D.alexanderSplitting g₀ x).2 = D.alexanderAugmentation x := by
  exact (LinearMap.congr_fun
    ((LinearMap.exact_subtype_ker_map D.alexanderAugmentation).splitSurjectiveEquiv
      (Submodule.injective_subtype _)
      ⟨LinearMap.toSpanSingleton ℤ[T;T⁻¹] D.AlexanderModule (D.alexanderGenerator g₀),
        by ext; simp⟩).2.2 x).symm

/-- The inverse splitting adds the reduced component to the chosen free component. -/
@[simp]
theorem alexanderSplitting_symm_apply (x : D.ReducedAlexanderModule) (r : ℤ[T;T⁻¹]) :
    (D.alexanderSplitting g₀).symm (x, r) =
      (x : D.AlexanderModule) + r • D.alexanderGenerator g₀ := by
  let S := (LinearMap.exact_subtype_ker_map D.alexanderAugmentation).splitSurjectiveEquiv
    (Submodule.injective_subtype _)
  let s := LinearMap.toSpanSingleton ℤ[T;T⁻¹] D.AlexanderModule (D.alexanderGenerator g₀)
  have hs : D.alexanderAugmentation.comp s = LinearMap.id := by ext; simp [s]
  have hi : (D.alexanderSplitting g₀).symm (x, 0) = (x : D.AlexanderModule) :=
    (LinearMap.congr_fun (S ⟨s, hs⟩).2.1 x).symm
  have hr : (D.alexanderSplitting g₀).symm (0, r) = r • D.alexanderGenerator g₀ :=
    LinearMap.congr_fun (congrArg Subtype.val (S.left_inv ⟨s, hs⟩)) r
  calc
    (D.alexanderSplitting g₀).symm (x, r) =
        (D.alexanderSplitting g₀).symm (x, 0) +
          (D.alexanderSplitting g₀).symm (0, r) := by rw [← map_add]; simp
    _ = _ := by rw [hi, hr]

/-- The kernel component of the splitting is the reduction projection. -/
@[simp]
theorem alexanderSplitting_fst (x : D.AlexanderModule) :
    (D.alexanderSplitting g₀ x).1 = D.alexanderReduction g₀ x := by
  apply Subtype.ext
  have h := (D.alexanderSplitting g₀).symm_apply_apply x
  rw [alexanderSplitting_symm_apply, alexanderSplitting_snd] at h
  exact (eq_sub_iff_add_eq.mpr h).trans (D.coe_alexanderReduction g₀ x).symm

/-- The elementary ideals shifted by one are the Fitting ideals of the augmentation kernel,
including for the empty diagram, where both ideals are `⊤`. -/
theorem elementaryIdeal_succ_eq_fittingIdeal_reduced (k : ℕ) :
    D.elementaryIdeal (k + 1) = fittingIdeal ℤ[T;T⁻¹] D.ReducedAlexanderModule k := by
  classical
  by_cases h : Nonempty (Fin (4 * n) ⊕ Fin D.crossinglessComponentCount)
  · rw [D.elementaryIdeal_def, fittingIdeal_congr (D.alexanderSplitting (Classical.choice h))]
    simpa using fittingIdeal_prod_add_finrank ℤ[T;T⁻¹] D.ReducedAlexanderModule ℤ[T;T⁻¹] k
  · have : IsEmpty (Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) :=
      not_nonempty_iff.mp h
    have : Subsingleton D.AlexanderModule := D.alexanderModuleMk_surjective.subsingleton
    have : Subsingleton D.ReducedAlexanderModule := inferInstance
    rw [D.elementaryIdeal_def,
      fittingIdeal_eq_top_of_surjective (φ := LinearMap.id) Function.surjective_id
        (by simp [Module.finrank_eq_zero_of_subsingleton]),
      fittingIdeal_eq_top_of_surjective (φ := LinearMap.id) Function.surjective_id
        (by simp [Module.finrank_eq_zero_of_subsingleton])]

end TauCeti.OrientedPDCode
