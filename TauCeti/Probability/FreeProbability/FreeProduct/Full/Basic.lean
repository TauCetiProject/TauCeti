/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.LinearAlgebra.FreeProduct.Star
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.l2Space
import TauCeti.Analysis.CStarAlgebra.Quotient
import TauCeti.Analysis.CStarAlgebra.Representation.Compression
import TauCeti.Analysis.CStarAlgebra.Representation.GNS
import TauCeti.Analysis.CStarAlgebra.Seminorm
import TauCeti.Analysis.CStarAlgebra.State.Spectrum
import TauCeti.Analysis.InnerProductSpace.StarAlgHom
import TauCeti.Probability.FreeProbability.FreeProduct.Reduced

/-!
# The full unital C⋆-free product

Let `(A i)_{i : I}` (`I : Type u`, `A : I → Type v`) be a family of unital complex C⋆-algebras.
The *universal* (or *full*) C⋆-seminorm on the algebraic star free product
`LinearAlgebra.FreeProduct ℂ A` is

`FullFreeProduct.seminorm A x = sup ‖π x‖`,

where `π` ranges over unital `⋆`-representations of `LinearAlgebra.FreeProduct ℂ A` on Hilbert
spaces in universe `max u v`. Because every cyclic subspace of a Hilbert-space representation of
`LinearAlgebra.FreeProduct ℂ A` in any universe is isometric to a Hilbert space in universe
`max u v` (`AlgHom.exists_isometry_mapsTo_mem_range`), this supremum bounds all Hilbert-space
representations (`FullFreeProduct.norm_representation_le_seminorm`) and hence, by Gelfand–Naimark,
all unital `⋆`-homomorphisms into unital C⋆-algebras in any universe
(`FullFreeProduct.norm_starAlgHom_le_seminorm`).

Completing `LinearAlgebra.FreeProduct ℂ A` in `FullFreeProduct.seminorm A` (via the seminormed type
synonym `FullFreeProduct.Algebraic A`) yields the *full unital C⋆-free product*
`FullFreeProduct A`, a unital C⋆-algebra in universe `max u v` satisfying the coproduct universal
property `FullFreeProduct.lift : ((i : I) → A i →⋆ₐ[ℂ] B) ≃ (FullFreeProduct A →⋆ₐ[ℂ] B)` for any
unital C⋆-algebra `B` in any universe `w`.

When every factor `A i` is nontrivial, no faithful state on any `A i` is required to embed the
factors isometrically: for `a : A i₀`, pairing a norm-attaining state for `star a * a` on `A i₀`
with arbitrary states on the remaining factors in `ReducedFreeProduct.representation` shows
`FullFreeProduct.seminorm A (ι ℂ A i₀ a) = ‖a‖`, so `FullFreeProduct.factor i₀` is isometric and
injective (`FullFreeProduct.isometry_factor`, `FullFreeProduct.factor_injective`), and
`Nontrivial (FullFreeProduct A) ↔ ∀ i, Nontrivial (A i)` (`FullFreeProduct.nontrivial_iff`).

Functoriality, relabeling, and grouping equivalences are developed in
`TauCeti.Probability.FreeProbability.FreeProduct.Full.Functoriality`, and the canonical quotient
onto the reduced C⋆-free product together with the pulled-back vacuum state are developed in
`TauCeti.Probability.FreeProbability.FreeProduct.Full.Reduced`.

## Main definitions

* `TauCeti.FullFreeProduct.seminorm`: the universal C⋆-seminorm on `LinearAlgebra.FreeProduct ℂ A`.
* `TauCeti.FullFreeProduct.Algebraic`: `LinearAlgebra.FreeProduct ℂ A` with the universal seminorm.
* `TauCeti.FullFreeProduct`: the full unital C⋆-free product of `A`, a unital C⋆-algebra.
* `TauCeti.FullFreeProduct.ofAlgebraic` and `TauCeti.FullFreeProduct.factor`: canonical dense
  algebraic map and factor homomorphisms.
* `TauCeti.FullFreeProduct.liftAlgebraic`, `TauCeti.FullFreeProduct.liftRepresentation`,
  `TauCeti.FullFreeProduct.lift`, and `TauCeti.FullFreeProduct.congrAlgebraic`: universal properties
  in arbitrary target universes and lifting of algebraic `⋆`-isomorphisms.

## Main statements

* `TauCeti.FullFreeProduct.norm_representation_le_seminorm` and
  `TauCeti.FullFreeProduct.norm_starAlgHom_le_seminorm`: universe-independent upper bounds.
* `TauCeti.FullFreeProduct.seminorm_ι`, `TauCeti.FullFreeProduct.isometry_factor`,
  `TauCeti.FullFreeProduct.factor_injective`, and `TauCeti.FullFreeProduct.nontrivial_iff`.

## References

* D. Voiculescu, *Symmetries of some reduced free product C⋆-algebras*, Lecture Notes in Math.
  1132, Springer, 1985, pp. 556–588.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §§1.4–1.5.
* B. Blackadar, *Operator Algebras: Theory of C⋆-Algebras and von Neumann Algebras*, §II.8.3.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.4.
-/

public section

noncomputable section

open LinearAlgebra.FreeProduct UniformSpace
open scoped ComplexOrder InnerProductSpace

namespace TauCeti

universe u v w

section SeminormAndCompletion

variable {I : Type u} [DecidableEq I] (A : I → Type v) [∀ i, CStarAlgebra (A i)]

namespace FullFreeProduct

/-- The seminorms `x ↦ ‖π x‖` on `LinearAlgebra.FreeProduct ℂ A` induced by unital
`⋆`-representations on Hilbert spaces in universe `max u v`. -/
private def representationSeminorms : Set (Seminorm ℂ (LinearAlgebra.FreeProduct ℂ A)) :=
  {p | ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)),
      p = (normSeminorm ℂ (H →L[ℂ] H)).comp
        (π : LinearAlgebra.FreeProduct ℂ A →ₗ[ℂ] (H →L[ℂ] H))}

/-- Every algebraic free-product element is uniformly bounded across all Hilbert-space
representations, since each factor restriction is contractive. -/
private theorem exists_representation_bound (x : LinearAlgebra.FreeProduct ℂ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H : Type (max u v)) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)), ‖π x‖ ≤ C := by
  induction x using LinearAlgebra.FreeProduct.induction_on with
  | algebraMap r =>
    refine ⟨‖r‖, norm_nonneg r, fun H _ _ _ π => ?_⟩
    rw [AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_def]
    exact (norm_smul_le r (ContinuousLinearMap.id ℂ H)).trans
      (mul_le_of_le_one_right (norm_nonneg r) ContinuousLinearMap.norm_id_le)
  | ι i a =>
    refine ⟨‖a‖, norm_nonneg a, fun H _ _ _ π => ?_⟩
    rw [← ιStar_apply, ← StarAlgHom.comp_apply]
    exact NonUnitalStarAlgHom.norm_apply_le (π.comp (ιStar ℂ A i)).toNonUnitalStarAlgHom a
  | mul x y ihx ihy =>
    obtain ⟨Cx, hCx0, hCx⟩ := ihx
    obtain ⟨Cy, hCy0, hCy⟩ := ihy
    refine ⟨Cx * Cy, mul_nonneg hCx0 hCy0, fun H _ _ _ π => ?_⟩
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (hCx H π) (hCy H π) (norm_nonneg _) hCx0)
  | add x y ihx ihy =>
    obtain ⟨Cx, hCx0, hCx⟩ := ihx
    obtain ⟨Cy, hCy0, hCy⟩ := ihy
    refine ⟨Cx + Cy, add_nonneg hCx0 hCy0, fun H _ _ _ π => ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hCx H π) (hCy H π))

private theorem bddAbove_representationSeminorms : BddAbove (representationSeminorms A) := by
  rw [Seminorm.bddAbove_iff]
  choose bound _ hbound using exists_representation_bound A
  refine ⟨bound, ?_⟩
  rintro _ ⟨_, ⟨H, _, _, _, π, rfl⟩, rfl⟩ x
  exact hbound x H π

/-- The universal C⋆-seminorm `‖x‖ᵤ = sup ‖π x‖` on `LinearAlgebra.FreeProduct ℂ A`: the supremum
of operator norms over all unital `⋆`-representations on Hilbert spaces in universe `max u v`. -/
def seminorm : Seminorm ℂ (LinearAlgebra.FreeProduct ℂ A) :=
  sSup (representationSeminorms A)

section SeminormAPI

variable {A}

theorem seminorm_apply (x : LinearAlgebra.FreeProduct ℂ A) :
    seminorm A x =
      sSup {r : ℝ | ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)),
          ‖π x‖ = r} := by
  rw [seminorm, Seminorm.sSup_apply (bddAbove_representationSeminorms A), iSup]
  congr 1
  ext r
  simp [representationSeminorms]

/-- Every unital Hilbert-space representation of `LinearAlgebra.FreeProduct ℂ A`, on a Hilbert space
in *any* universe `w`, is bounded by `FullFreeProduct.seminorm A`. -/
theorem norm_representation_le_seminorm {H : Type w} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (x : LinearAlgebra.FreeProduct ℂ A) :
    ‖π x‖ ≤ seminorm A x := by
  refine (π x).opNorm_le_bound (apply_nonneg _ x) fun ξ => ?_
  obtain ⟨K, _, _, _, V, hV, η, rfl⟩ := π.toAlgHom.exists_isometry_mapsTo_mem_range ξ
  let p : Seminorm ℂ (LinearAlgebra.FreeProduct ℂ A) :=
    (normSeminorm ℂ (K →L[ℂ] K)).comp
      (π.compression V hV : LinearAlgebra.FreeProduct ℂ A →ₗ[ℂ] (K →L[ℂ] K))
  have hp : p ∈ representationSeminorms A := ⟨K, _, _, _, π.compression V hV, rfl⟩
  have hK : p ≤ seminorm A := le_csSup (bddAbove_representationSeminorms A) hp
  rw [← π.apply_compression_apply V hV, V.norm_map, V.norm_map]
  exact (π.compression V hV x).le_of_opNorm_le (hK x) η

/-- Every unital `⋆`-homomorphism from `LinearAlgebra.FreeProduct ℂ A` into any unital C⋆-algebra
`B` (in any universe `w`) is bounded by `FullFreeProduct.seminorm A`. -/
theorem norm_starAlgHom_le_seminorm {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) (x : LinearAlgebra.FreeProduct ℂ A) :
    ‖ρ x‖ ≤ seminorm A x := by
  obtain ⟨H, _, _, _, π, hπ⟩ := TauCeti.CStarAlgebra.exists_faithful_representation B
  rw [← NonUnitalStarAlgHom.norm_map π hπ]
  exact norm_representation_le_seminorm (π.comp ρ) x

/-- Characterization of `seminorm A x ≤ c` via Hilbert-space representations in universe
`max u v`. -/
theorem seminorm_le_iff_hilbert {x : LinearAlgebra.FreeProduct ℂ A} {c : ℝ} :
    seminorm A x ≤ c ↔
      ∀ (H : Type (max u v)) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)), ‖π x‖ ≤ c := by
  refine ⟨fun h _ _ _ _ π => (norm_representation_le_seminorm π x).trans h, fun h => ?_⟩
  have hc : 0 ≤ c := by
    let H := lp (fun _ : PEmpty.{max u v + 1} => ℂ) 2
    let π₀ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H) :=
      liftStar fun {i} =>
        { toFun _ := 0
          map_one' := Subsingleton.elim _ _
          map_mul' _ _ := Subsingleton.elim _ _
          map_zero' := Subsingleton.elim _ _
          map_add' _ _ := Subsingleton.elim _ _
          commutes' _ := Subsingleton.elim _ _
          map_star' _ := Subsingleton.elim _ _ }
    exact (norm_nonneg _).trans (h H π₀)
  exact Seminorm.sSup_apply_le (bddAbove_representationSeminorms A) hc
    fun _ ⟨H, _, _, _, π, hp⟩ => hp ▸ h H π

/-- Characterization of `seminorm A x ≤ c` via unital `⋆`-homomorphisms into unital C⋆-algebras in
universe `max u v`. -/
theorem seminorm_le_iff {x : LinearAlgebra.FreeProduct ℂ A} {c : ℝ} :
    seminorm A x ≤ c ↔
      ∀ (B : Type (max u v)) [CStarAlgebra B]
        (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B), ‖ρ x‖ ≤ c :=
  ⟨fun h _ _ ρ => (norm_starAlgHom_le_seminorm ρ x).trans h,
    fun h => seminorm_le_iff_hilbert.2 fun H _ _ _ π => h (H →L[ℂ] H) π⟩

/-- The universal seminorm is submultiplicative. -/
theorem seminorm_mul_le (x y : LinearAlgebra.FreeProduct ℂ A) :
    seminorm A (x * y) ≤ seminorm A x * seminorm A y :=
  Seminorm.sSup_mul_le (bddAbove_representationSeminorms A) (fun _ ⟨_, _, _, _, π, hp⟩ x y => by
    simpa [hp] using norm_mul_le (π x) (π y)) x y

/-- The universal seminorm is invariant under the involution. -/
@[simp]
theorem seminorm_star (x : LinearAlgebra.FreeProduct ℂ A) :
    seminorm A (star x) = seminorm A x :=
  Seminorm.sSup_star (bddAbove_representationSeminorms A) (fun _ ⟨_, _, _, _, π, hp⟩ x => by
    simp [hp, map_star]) x

/-- The universal seminorm satisfies the C⋆-identity `‖x⋆ * x‖ᵤ = ‖x‖ᵤ * ‖x‖ᵤ`. -/
theorem seminorm_star_mul_self (x : LinearAlgebra.FreeProduct ℂ A) :
    seminorm A (star x * x) = seminorm A x * seminorm A x :=
  Seminorm.sSup_star_mul_self (bddAbove_representationSeminorms A)
    (fun _ ⟨_, _, _, _, π, hp⟩ x => by simp [hp, map_star, CStarRing.norm_star_mul_self]) x

theorem seminorm_one_le : seminorm A 1 ≤ 1 :=
  seminorm_le_iff_hilbert.2 fun _ _ _ _ π => by
    rw [map_one, ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le

theorem seminorm_ι_le (i : I) (a : A i) : seminorm A (ι ℂ A i a) ≤ ‖a‖ :=
  seminorm_le_iff_hilbert.2 fun _ _ _ _ π => by
    rw [← ιStar_apply, ← StarAlgHom.comp_apply]
    exact NonUnitalStarAlgHom.norm_apply_le (π.comp (ιStar ℂ A i)).toNonUnitalStarAlgHom a

/-- When every factor C⋆-algebra `A i` is nontrivial, the universal C⋆-seminorm is isometric on
each canonical factor map `ι ℂ A i₀`. No faithful state on any factor is required: we pair a
norm-attaining state for `star a * a` on `A i₀` with arbitrary states on the remaining factors in
the reduced free-product GNS representation. -/
@[simp]
theorem seminorm_ι [∀ i, Nontrivial (A i)] (i₀ : I) (a : A i₀) :
    seminorm A (ι ℂ A i₀ a) = ‖a‖ := by
  refine le_antisymm (seminorm_ι_le i₀ a) ?_
  choose φ hφ hφb using fun i =>
    TauCeti.CStarAlgebra.exists_starPositiveFunctional_apply_star_mul_self_eq_norm_sq
      (if h : i = i₀ then h ▸ a else (1 : A i))
  let π := ReducedFreeProduct.representation φ hφ
  let Ω := ReducedFreeProduct.vacuum φ hφ
  have hω₀ : φ i₀ (star a * a) = (‖a‖ : ℂ) ^ 2 := by simpa using hφb i₀
  have hsq : ‖π (ι ℂ A i₀ a) Ω‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [π.norm_sq_apply_eq_re_inner_star_mul Ω (ι ℂ A i₀ a), star_ι, ← map_mul (ι ℂ A i₀)]
    have hinner : ⟪Ω, π (ι ℂ A i₀ (star a * a)) Ω⟫_ℂ = φ i₀ (star a * a) := by
      rw [← ReducedFreeProduct.coe_ofAlgebraic φ hφ, ← ReducedFreeProduct.state_apply φ hφ,
        ReducedFreeProduct.state_ofAlgebraic, freeProductPositiveFunctional_ι]
    rw [hinner, hω₀, ← Complex.ofReal_pow]
    exact Complex.ofReal_re (‖a‖ ^ 2)
  have hvec : ‖π (ι ℂ A i₀ a) Ω‖ = ‖a‖ := by
    have h1 := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1
  calc ‖a‖ = ‖π (ι ℂ A i₀ a) Ω‖ := hvec.symm
    _ ≤ ‖π (ι ℂ A i₀ a)‖ * ‖Ω‖ := (π (ι ℂ A i₀ a)).le_opNorm Ω
    _ = ‖π (ι ℂ A i₀ a)‖ := by rw [ReducedFreeProduct.norm_vacuum φ hφ, mul_one]
    _ ≤ seminorm A (ι ℂ A i₀ a) := norm_representation_le_seminorm π (ι ℂ A i₀ a)

@[simp]
theorem seminorm_one [∀ i, Nontrivial (A i)] : seminorm A 1 = 1 := by
  refine le_antisymm seminorm_one_le ?_
  choose φ hφ _ using fun i =>
    TauCeti.CStarAlgebra.exists_starPositiveFunctional_apply_star_mul_self_eq_norm_sq (1 : A i)
  let π := ReducedFreeProduct.representation φ hφ
  let Ω := ReducedFreeProduct.vacuum φ hφ
  calc (1 : ℝ) = ‖Ω‖ := (ReducedFreeProduct.norm_vacuum φ hφ).symm
    _ = ‖π 1 Ω‖ := by rw [map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
    _ ≤ ‖π 1‖ * ‖Ω‖ := (π 1).le_opNorm Ω
    _ = ‖π 1‖ := by rw [ReducedFreeProduct.norm_vacuum φ hφ, mul_one]
    _ ≤ seminorm A 1 := norm_representation_le_seminorm π 1

end SeminormAPI

/-- The algebraic star free product `LinearAlgebra.FreeProduct ℂ A` equipped with the universal
C⋆-seminorm `FullFreeProduct.seminorm A` as its norm. Its completion is `FullFreeProduct A`. Use
`FullFreeProduct.Algebraic.equiv` to pass to and from `LinearAlgebra.FreeProduct ℂ A`. -/
@[expose] def Algebraic : Type (max u v) :=
  LinearAlgebra.FreeProduct ℂ A

namespace Algebraic

instance : Ring (Algebraic A) :=
  inferInstanceAs (Ring (LinearAlgebra.FreeProduct ℂ A))

instance : Algebra ℂ (Algebraic A) :=
  inferInstanceAs (Algebra ℂ (LinearAlgebra.FreeProduct ℂ A))

instance : StarRing (Algebraic A) :=
  inferInstanceAs (StarRing (LinearAlgebra.FreeProduct ℂ A))

instance : StarModule ℂ (Algebraic A) :=
  inferInstanceAs (StarModule ℂ (LinearAlgebra.FreeProduct ℂ A))

/-- `Algebraic A` is `LinearAlgebra.FreeProduct ℂ A` as a unital `⋆`-algebra. -/
def equiv : LinearAlgebra.FreeProduct ℂ A ≃⋆ₐ[ℂ] Algebraic A :=
  StarAlgEquiv.refl ℂ (LinearAlgebra.FreeProduct ℂ A)

instance : SeminormedAddCommGroup (Algebraic A) :=
  @AddGroupSeminorm.toSeminormedAddCommGroup (Algebraic A) _ (seminorm A).toAddGroupSeminorm

variable {A}

@[simp]
theorem norm_equiv (x : LinearAlgebra.FreeProduct ℂ A) : ‖equiv A x‖ = seminorm A x :=
  (rfl)

theorem norm_def (x : Algebraic A) : ‖x‖ = seminorm A ((equiv A).symm x) :=
  (rfl)

instance : SeminormedRing (Algebraic A) where
  __ : SeminormedAddCommGroup (Algebraic A) := inferInstance
  __ : Ring (Algebraic A) := inferInstance
  norm_mul_le := seminorm_mul_le (A := A)

instance : NormedAlgebra ℂ (Algebraic A) where
  __ : Algebra ℂ (Algebraic A) := inferInstance
  norm_smul_le c x := (map_smul_eq_mul (seminorm A) c x).le

instance : NormedStarGroup (Algebraic A) where
  norm_star_le x := (seminorm_star (A := A) x).le

theorem norm_star_mul_self (x : Algebraic A) : ‖star x * x‖ = ‖x‖ * ‖x‖ :=
  seminorm_star_mul_self (A := A) x

end Algebraic

end FullFreeProduct

/-- The full unital C⋆-free product `*_{i : I} A i` of a family of unital C⋆-algebras `A i`: the
Hausdorff completion of `LinearAlgebra.FreeProduct ℂ A` in its universal C⋆-seminorm. -/
@[expose] def FullFreeProduct : Type (max u v) :=
  Completion (FullFreeProduct.Algebraic A)

namespace FullFreeProduct

instance instCStarAlgebra : CStarAlgebra (FullFreeProduct A) :=
  letI : CStarAlgebra (Completion (Algebraic A)) :=
    { toCStarRing := Completion.cstarRing fun x => (Algebraic.norm_star_mul_self x).ge
      norm_smul_le := norm_smul_le }
  inferInstanceAs (CStarAlgebra (Completion (Algebraic A)))

/-- The canonical unital `⋆`-algebra homomorphism from the algebraic free product into the full
C⋆-free product, with dense range. -/
def ofAlgebraic : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] FullFreeProduct A where
  toFun x := (Algebraic.equiv A x : Completion (Algebraic A))
  map_one' := by
    rw [map_one]
    exact Completion.coe_one _
  map_mul' x y := by
    rw [map_mul]
    exact Completion.coe_mul' _ _
  map_zero' := by
    rw [map_zero]
    exact Completion.coe_zero
  map_add' x y := by
    rw [map_add]
    exact Completion.coe_add _ _
  commutes' r := by
    rw [AlgHomClass.commutes]
    exact (Completion.algebraMap_def _ _ r).symm
  map_star' x := by
    rw [map_star]
    exact Completion.coe_star _

section CoreAPI

variable {A}

@[simp]
theorem coe_equiv_eq_ofAlgebraic (x : LinearAlgebra.FreeProduct ℂ A) :
    ((Algebraic.equiv A x : Completion (Algebraic A)) : FullFreeProduct A) = ofAlgebraic A x :=
  (rfl)

@[simp]
theorem norm_ofAlgebraic (x : LinearAlgebra.FreeProduct ℂ A) :
    ‖ofAlgebraic A x‖ = seminorm A x :=
  (Completion.norm_coe (Algebraic.equiv A x)).trans (Algebraic.norm_equiv x)

instance [∀ i, Nontrivial (A i)] : NormOneClass (FullFreeProduct A) where
  norm_one := by rw [← map_one (ofAlgebraic A), norm_ofAlgebraic, seminorm_one]

/-- The image of the algebraic free product is norm dense in `FullFreeProduct A`. -/
theorem denseRange_ofAlgebraic : DenseRange (ofAlgebraic A) :=
  Completion.denseRange_coe.comp (Algebraic.equiv A).surjective.denseRange
    (Completion.continuous_coe _)

/-- Closed properties on `FullFreeProduct A` follow from their restriction to
`LinearAlgebra.FreeProduct ℂ A`. -/
@[elab_as_elim]
theorem induction_on {p : FullFreeProduct A → Prop} (x : FullFreeProduct A)
    (hp : IsClosed {x | p x}) (ih : ∀ a, p (ofAlgebraic A a)) : p x :=
  Completion.induction_on (p := p) x hp fun y => by
    have h := ih ((Algebraic.equiv A).symm y)
    rwa [← coe_equiv_eq_ofAlgebraic, StarAlgEquiv.apply_symm_apply] at h

/-- The canonical unital `⋆`-homomorphism from the `i`-th factor C⋆-algebra into
`FullFreeProduct A`. -/
def factor (i : I) : A i →⋆ₐ[ℂ] FullFreeProduct A :=
  (ofAlgebraic A).comp (ιStar ℂ A i)

-- Keep `factor` bundled under `simp` so factor-evaluation `@[simp]` lemmas (`lift_factor`,
-- `norm_factor`, `map_factor`, `toReduced_factor`, `state_factor`, etc.) stay in normal form.
theorem factor_apply (i : I) (a : A i) : factor i a = ofAlgebraic A (ι ℂ A i a) := by
  simp [factor]

@[simp]
theorem ofAlgebraic_comp_ιStar (i : I) : (ofAlgebraic A).comp (ιStar ℂ A i) = factor i :=
  (rfl)

@[simp]
theorem factor_toAlgHom (i : I) :
    (factor (A := A) i).toAlgHom = (ofAlgebraic A).toAlgHom.comp (ι ℂ A i) :=
  AlgHom.ext fun a => factor_apply i a

theorem norm_factor_le (i : I) (a : A i) : ‖factor (A := A) i a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le (factor i).toNonUnitalStarAlgHom a

/-- The star-subalgebra images of the factor maps generate `(ofAlgebraic A).range`. -/
theorem iSup_range_factor :
    (⨆ i, (factor (A := A) i).range) = (ofAlgebraic A).range := by
  refine le_antisymm (iSup_le fun i => ?_) ?_
  · rintro _ ⟨a, rfl⟩
    exact ⟨ι ℂ A i a, (factor_apply i a).symm⟩
  · have hmem : ∀ x, ofAlgebraic A x ∈ ⨆ i, (factor (A := A) i).range := fun x => by
      induction x using LinearAlgebra.FreeProduct.induction_on with
      | algebraMap r =>
        exact AlgHomClass.commutes (ofAlgebraic A) r ▸ StarSubalgebra.algebraMap_mem _ r
      | ι i a => exact le_iSup (fun j => (factor (A := A) j).range) i ⟨a, factor_apply i a⟩
      | mul x y ihx ihy => exact (map_mul (ofAlgebraic A) x y).symm ▸ mul_mem ihx ihy
      | add x y ihx ihy => exact (map_add (ofAlgebraic A) x y).symm ▸ add_mem ihx ihy
    rintro _ ⟨x, rfl⟩
    exact hmem x

/-- The canonical factor ranges generate `FullFreeProduct A` as a norm-closed star subalgebra. -/
theorem topologicalClosure_iSup_range_factor :
    (⨆ i, (factor (A := A) i).range).topologicalClosure = ⊤ := by
  rw [iSup_range_factor]
  apply SetLike.ext'
  have hcoe : ((ofAlgebraic A).range : Set (FullFreeProduct A)) = Set.range (ofAlgebraic A) :=
    (ofAlgebraic A).toAlgHom.coe_range
  rw [StarSubalgebra.topologicalClosure_coe, hcoe, (denseRange_ofAlgebraic (A := A)).closure_eq]
  rfl

/-- When every factor `A i` is nontrivial, each canonical factor map into `FullFreeProduct A`
preserves norms. -/
@[simp]
theorem norm_factor [∀ i, Nontrivial (A i)] (i : I) (a : A i) :
    ‖factor (A := A) i a‖ = ‖a‖ := by
  rw [factor_apply, norm_ofAlgebraic, seminorm_ι]

/-- When every factor `A i` is nontrivial, each canonical factor map into `FullFreeProduct A` is an
isometry. -/
theorem isometry_factor [∀ i, Nontrivial (A i)] (i : I) :
    Isometry (factor (A := A) i) :=
  AddMonoidHomClass.isometry_of_norm (factor i) (norm_factor i)

/-- When every factor `A i` is nontrivial, each canonical factor map into `FullFreeProduct A` is
injective. -/
theorem factor_injective [∀ i, Nontrivial (A i)] (i : I) :
    Function.Injective (factor (A := A) i) :=
  (isometry_factor i).injective

instance [∀ i, Nontrivial (A i)] : Nontrivial (FullFreeProduct A) :=
  NormOneClass.nontrivial

/-- The full unital C⋆-free product `FullFreeProduct A` is nontrivial if and only if every factor
`A i` is nontrivial (which holds vacuously when `I` is empty). -/
theorem nontrivial_iff : Nontrivial (FullFreeProduct A) ↔ ∀ i, Nontrivial (A i) :=
  ⟨fun _ i => (factor (A := A) i).toRingHom.domain_nontrivial, fun _ => inferInstance⟩

/-- Continuous linear maps out of `FullFreeProduct A` into a Hausdorff space are determined on
`ofAlgebraic A`. -/
@[ext]
theorem continuousLinearMap_ext {E : Type*} [TopologicalSpace E] [T2Space E] [AddCommMonoid E]
    [Module ℂ E] {S T : FullFreeProduct A →L[ℂ] E}
    (h : ∀ a, S (ofAlgebraic A a) = T (ofAlgebraic A a)) : S = T :=
  DFunLike.coe_injective <|
    (denseRange_ofAlgebraic (A := A)).equalizer S.continuous T.continuous (funext h)

open scoped _root_.CStarAlgebra in
/-- Unital `⋆`-homomorphisms from `FullFreeProduct A` into a C⋆-algebra are determined on
`ofAlgebraic A`. -/
theorem starAlgHom_ext_ofAlgebraic {B : Type w} [CStarAlgebra B]
    {Φ Ψ : FullFreeProduct A →⋆ₐ[ℂ] B} (h : Φ.comp (ofAlgebraic A) = Ψ.comp (ofAlgebraic A)) :
    Φ = Ψ :=
  StarAlgHom.ext fun x => induction_on x (isClosed_eq (map_continuous Φ) (map_continuous Ψ))
    fun y => congr($h y)

/-- Unital `⋆`-homomorphisms from `FullFreeProduct A` into a C⋆-algebra are determined by their
restrictions to the factors `factor i`. -/
@[ext]
theorem starAlgHom_ext {B : Type w} [CStarAlgebra B] {Φ Ψ : FullFreeProduct A →⋆ₐ[ℂ] B}
    (h : ∀ i a, Φ (factor i a) = Ψ (factor i a)) : Φ = Ψ :=
  starAlgHom_ext_ofAlgebraic <| LinearAlgebra.FreeProduct.starAlgHom_ext fun i a => by
    simpa only [StarAlgHom.comp_apply, ← factor_apply] using h i a

private def extendAlgebraic {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) : FullFreeProduct A →⋆ₐ[ℂ] B :=
  (ρ.comp (Algebraic.equiv A).symm.toStarAlgHom).fromCompletion <|
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => by
      simpa [Algebraic.norm_def] using
        norm_starAlgHom_le_seminorm ρ ((Algebraic.equiv A).symm x)

private theorem extendAlgebraic_ofAlgebraic {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) (a : LinearAlgebra.FreeProduct ℂ A) :
    extendAlgebraic ρ (ofAlgebraic A a) = ρ a := by
  rw [← coe_equiv_eq_ofAlgebraic]
  -- `extendAlgebraic ρ` is by definition `StarAlgHom.fromCompletion` on `Completion (Algebraic A)`.
  exact (StarAlgHom.fromCompletion_apply_coe _ _ (Algebraic.equiv A a)).trans (by simp)

/-- `FullFreeProduct A` is the universal unital C⋆-envelope of `LinearAlgebra.FreeProduct ℂ A`:
unital `⋆`-homomorphisms out of `LinearAlgebra.FreeProduct ℂ A` into any unital C⋆-algebra `B`
(in any universe `w`) correspond bijectively to unital `⋆`-homomorphisms out of
`FullFreeProduct A`. -/
def liftAlgebraic {B : Type w} [CStarAlgebra B] :
    (LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) ≃ (FullFreeProduct A →⋆ₐ[ℂ] B) where
  toFun := extendAlgebraic
  invFun Φ := Φ.comp (ofAlgebraic A)
  left_inv ρ := StarAlgHom.ext (extendAlgebraic_ofAlgebraic ρ)
  right_inv Φ := starAlgHom_ext_ofAlgebraic
    (StarAlgHom.ext (extendAlgebraic_ofAlgebraic (Φ.comp (ofAlgebraic A))))

@[simp]
theorem liftAlgebraic_ofAlgebraic {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) (a : LinearAlgebra.FreeProduct ℂ A) :
    liftAlgebraic ρ (ofAlgebraic A a) = ρ a :=
  extendAlgebraic_ofAlgebraic ρ a

@[simp]
theorem liftAlgebraic_comp_ofAlgebraic {B : Type w} [CStarAlgebra B]
    (ρ : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] B) :
    (liftAlgebraic ρ).comp (ofAlgebraic A) = ρ :=
  liftAlgebraic.symm_apply_apply ρ

@[simp]
theorem liftAlgebraic_symm_apply {B : Type w} [CStarAlgebra B] (Φ : FullFreeProduct A →⋆ₐ[ℂ] B) :
    liftAlgebraic.symm Φ = Φ.comp (ofAlgebraic A) :=
  (rfl)

/-- Extend a unital Hilbert-space representation of `LinearAlgebra.FreeProduct ℂ A` (in any
universe `w`) by continuity to a unital `⋆`-representation of `FullFreeProduct A`. -/
def liftRepresentation {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    FullFreeProduct A →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  liftAlgebraic (B := H →L[ℂ] H) π

@[simp]
theorem liftRepresentation_ofAlgebraic {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (x : LinearAlgebra.FreeProduct ℂ A) :
    liftRepresentation π (ofAlgebraic A x) = π x :=
  liftAlgebraic_ofAlgebraic (B := H →L[ℂ] H) π x

@[simp]
theorem liftRepresentation_factor {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) (i : I) (a : A i) :
    liftRepresentation π (factor i a) = π (ι ℂ A i a) := by
  rw [factor_apply, liftRepresentation_ofAlgebraic]

open scoped _root_.CStarAlgebra in
/-- The range of `liftRepresentation π` is the norm closure of the algebraic image `π.range`. -/
theorem range_liftRepresentation {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (liftRepresentation π).range = π.range.topologicalClosure := by
  apply SetLike.ext'
  have hcoeL : ((liftRepresentation π).range : Set (H →L[ℂ] H)) =
      Set.range (liftRepresentation π) :=
    (liftRepresentation π).toAlgHom.coe_range
  have hcoe : (π.range : Set (H →L[ℂ] H)) = Set.range π := π.toAlgHom.coe_range
  rw [hcoeL, StarSubalgebra.topologicalClosure_coe, hcoe]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine induction_on x (isClosed_closure.preimage (map_continuous (liftRepresentation π)))
      fun a => ?_
    rw [liftRepresentation_ofAlgebraic]
    exact subset_closure ⟨a, rfl⟩
  · refine (liftRepresentation π).isClosed_setRange.closure_subset_iff.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨ofAlgebraic A a, liftRepresentation_ofAlgebraic π a⟩

/-- Membership in `(liftRepresentation π).range` is membership in the norm closure of
`Set.range π`. -/
theorem mem_range_liftRepresentation_iff {H : Type w} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    T ∈ (liftRepresentation π).range ↔ T ∈ closure (Set.range π) := by
  have hcoe : (π.range : Set (H →L[ℂ] H)) = Set.range π := π.toAlgHom.coe_range
  rw [range_liftRepresentation, ← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe, hcoe]

/-- Universal coproduct property of the full unital C⋆-free product: families of unital
`⋆`-homomorphisms `f : (i : I) → A i →⋆ₐ[ℂ] B` into any unital C⋆-algebra `B` (in any universe `w`)
correspond bijectively to unital `⋆`-homomorphisms `FullFreeProduct A →⋆ₐ[ℂ] B`. -/
def lift {B : Type w} [CStarAlgebra B] :
    ((i : I) → A i →⋆ₐ[ℂ] B) ≃ (FullFreeProduct A →⋆ₐ[ℂ] B) :=
  ({ toFun := fun f {i} => f i
     invFun := fun f i => f (i := i)
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } :
    ((i : I) → A i →⋆ₐ[ℂ] B) ≃ ({i : I} → A i →⋆ₐ[ℂ] B)).trans
    (liftStar.trans liftAlgebraic)

theorem lift_eq_liftAlgebraic {B : Type w} [CStarAlgebra B] (f : (i : I) → A i →⋆ₐ[ℂ] B) :
    lift f = liftAlgebraic (liftStar fun {i} => f i) :=
  (rfl)

@[simp]
theorem lift_ofAlgebraic {B : Type w} [CStarAlgebra B] (f : (i : I) → A i →⋆ₐ[ℂ] B)
    (x : LinearAlgebra.FreeProduct ℂ A) :
    lift f (ofAlgebraic A x) = liftStar (fun {i} => f i) x :=
  liftAlgebraic_ofAlgebraic _ x

@[simp]
theorem lift_factor {B : Type w} [CStarAlgebra B] (f : (i : I) → A i →⋆ₐ[ℂ] B) (i : I) (a : A i) :
    lift f (factor i a) = f i a := by
  rw [factor_apply, lift_ofAlgebraic, liftStar_ι]

@[simp]
theorem lift_comp_factor {B : Type w} [CStarAlgebra B] (f : (i : I) → A i →⋆ₐ[ℂ] B) (i : I) :
    (lift f).comp (factor i) = f i :=
  StarAlgHom.ext (lift_factor f i)

@[simp]
theorem lift_symm_apply {B : Type w} [CStarAlgebra B] (Φ : FullFreeProduct A →⋆ₐ[ℂ] B) (i : I) :
    lift.symm Φ i = Φ.comp (factor i) := by
  ext a
  simp [lift, factor_apply]

@[simp]
theorem lift_factor_eq_id :
    lift (factor (A := A)) = StarAlgHom.id ℂ (FullFreeProduct A) := by
  ext i a
  simp

@[simp]
theorem lift_comp {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
    (f : (i : I) → A i →⋆ₐ[ℂ] B) (g : B →⋆ₐ[ℂ] C) :
    lift (fun i => g.comp (f i)) = g.comp (lift f) := by
  ext i a
  simp

theorem norm_lift_le {B : Type w} [CStarAlgebra B] (f : (i : I) → A i →⋆ₐ[ℂ] B)
    (x : FullFreeProduct A) : ‖lift f x‖ ≤ ‖x‖ :=
  NonUnitalStarAlgHom.norm_apply_le (lift f).toNonUnitalStarAlgHom x

/-- The norm of `x : FullFreeProduct A` is the least upper bound of `‖liftAlgebraic π x‖` over all
Hilbert-space representations `π` in universe `max u v`. -/
theorem norm_le_iff_hilbert {x : FullFreeProduct A} {c : ℝ} :
    ‖x‖ ≤ c ↔
      ∀ (H : Type (max u v)) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)),
        ‖liftAlgebraic π x‖ ≤ c := by
  refine ⟨fun h H _ _ _ π => (NonUnitalStarAlgHom.norm_apply_le _ x).trans h, fun h => ?_⟩
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, ha⟩ := (denseRange_ofAlgebraic (A := A)).exists_dist_lt x (half_pos hε)
  have ha' : ‖x - ofAlgebraic A a‖ < ε / 2 := by rwa [← dist_eq_norm]
  have hac : ‖ofAlgebraic A a‖ ≤ c + ε / 2 := by
    rw [norm_ofAlgebraic, seminorm_le_iff_hilbert]
    intro H _ _ _ π
    rw [← liftAlgebraic_ofAlgebraic π a]
    calc ‖liftAlgebraic π (ofAlgebraic A a)‖
        ≤ ‖liftAlgebraic π x‖ + ‖liftAlgebraic π (x - ofAlgebraic A a)‖ := by
          rw [map_sub, norm_sub_rev]
          exact norm_le_insert' _ _
      _ ≤ c + ε / 2 :=
          add_le_add (h H π) ((NonUnitalStarAlgHom.norm_apply_le _ _).trans ha'.le)
  calc ‖x‖ ≤ ‖ofAlgebraic A a‖ + ‖x - ofAlgebraic A a‖ := norm_le_insert' x (ofAlgebraic A a)
    _ < c + ε := by linarith

/-- Two algebraic free-product elements map to the same element of `FullFreeProduct A` if and only
if they agree in every Hilbert-space representation in universe `max u v`. -/
theorem ofAlgebraic_eq_iff {a b : LinearAlgebra.FreeProduct ℂ A} :
    ofAlgebraic A a = ofAlgebraic A b ↔
      ∀ (H : Type (max u v)) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)), π a = π b := by
  refine ⟨fun h H _ _ _ π => by simpa using congr(liftAlgebraic π $h), fun h => ?_⟩
  rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, norm_ofAlgebraic]
  refine le_antisymm (seminorm_le_iff_hilbert.2 fun H _ _ _ π => ?_) (apply_nonneg _ _)
  rw [map_sub, h H π, sub_self, norm_zero]

/-- Any unital `⋆`-algebra equivalence between algebraic free products of unital C⋆-algebras lifts
canonically to an isometric `⋆`-isomorphism between their full unital C⋆-free products. -/
def congrAlgebraic {J : Type*} [DecidableEq J] {B : J → Type*} [∀ j, CStarAlgebra (B j)]
    (e : LinearAlgebra.FreeProduct ℂ A ≃⋆ₐ[ℂ] LinearAlgebra.FreeProduct ℂ B) :
    FullFreeProduct A ≃⋆ₐ[ℂ] FullFreeProduct B :=
  StarAlgEquiv.ofStarAlgHom
    (liftAlgebraic ((ofAlgebraic B).comp e.toStarAlgHom))
    (liftAlgebraic ((ofAlgebraic A).comp e.symm.toStarAlgHom))
    (starAlgHom_ext_ofAlgebraic <| StarAlgHom.ext fun x => by simp)
    (starAlgHom_ext_ofAlgebraic <| StarAlgHom.ext fun y => by simp)

@[simp]
theorem congrAlgebraic_ofAlgebraic {J : Type*} [DecidableEq J] {B : J → Type*}
    [∀ j, CStarAlgebra (B j)]
    (e : LinearAlgebra.FreeProduct ℂ A ≃⋆ₐ[ℂ] LinearAlgebra.FreeProduct ℂ B)
    (x : LinearAlgebra.FreeProduct ℂ A) :
    congrAlgebraic e (ofAlgebraic A x) = ofAlgebraic B (e x) := by
  simp [congrAlgebraic]

@[simp]
theorem congrAlgebraic_symm {J : Type*} [DecidableEq J] {B : J → Type*} [∀ j, CStarAlgebra (B j)]
    (e : LinearAlgebra.FreeProduct ℂ A ≃⋆ₐ[ℂ] LinearAlgebra.FreeProduct ℂ B) :
    (congrAlgebraic e).symm = congrAlgebraic e.symm :=
  (rfl)

end CoreAPI

end FullFreeProduct

end SeminormAndCompletion

end TauCeti
