/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Multiplier
public import TauCeti.Analysis.CStarAlgebra.Action.Ideal

/-!
# Quotient descent of covariant representations and multiplier homomorphisms

Let `q : CStarAction.Hom α β` be a surjective equivariant `⋆`-homomorphism from `(A, G, α)` onto
`(B, G, β)` (for instance, the canonical quotient projection `α.quotientMkHom I hI` modulo a closed
`α`-invariant two-sided ideal `I`).

* Every covariant representation `P : CovariantRepresentation α H` whose coefficient representation
  annihilates `ker q` descends uniquely to `P.descend q hq hker : CovariantRepresentation β H` on
  the same Hilbert space `H`, keeping `P.group` unchanged and satisfying
  `(P.descend q hq hker).comap q = P`.
* Every multiplier-valued covariant homomorphism `M : CovariantMultiplierHom α C` into `𝓜(ℂ, C)`
  whose coefficient map annihilates `ker q` descends uniquely to
  `M.descend q hq hker : CovariantMultiplierHom β C` with `(M.descend q hq hker).comap q = M`,
  preserving multiplier nondegeneracy, pushforwards along nondegenerate multiplier homomorphisms,
  Hilbert-space extensions, and Bochner integration on `C_c(G, A)`.

Specializing `q` to `α.quotientMkHom I hI` gives `CovariantRepresentation.quotientLift` and
`CovariantMultiplierHom.quotientLift` on concrete quotient actions `α.quotient I hI`. Together with
`CovariantRepresentation.idealExtension`, these constructions classify covariant pairs of `α`
according to their restriction to an invariant ideal `I` and descent to `A ⧸ I`, with no universe
restriction on the Hilbert space or target C⋆-algebra.

## Main declarations

* `TauCeti.CStarAction.CovariantRepresentation.descend` and
  `TauCeti.CStarAction.CovariantRepresentation.quotientLift`: descent of Hilbert-space covariant
  representations along surjective equivariant homomorphisms and C⋆-quotients, with uniqueness
  (`eq_descend_iff`, `exists_comap_eq_iff`, `eq_quotientLift_iff`,
  `exists_comap_quotientMkHom_eq_iff`) and integration compatibility.
* `TauCeti.CStarAction.CovariantMultiplierHom.descend` and
  `TauCeti.CStarAction.CovariantMultiplierHom.quotientLift`: descent of multiplier-valued covariant
  homomorphisms into `𝓜(ℂ, C)`, with uniqueness (`eq_descend_iff`, `exists_comap_eq_iff`,
  `eq_quotientLift_iff`, `exists_comap_quotientMkHom_eq_iff`), pushforward compatibility
  (`map_descend`, `toCovariantRepresentation_descend`), and strict Bochner integration
  compatibility.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 3.19.
* Iain Raeburn, *On crossed products and Takai duality*, Proc. Edinburgh Math. Soc. 31 (1988),
  321–330.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CStarAlgebra MultiplierAlgebra

namespace TauCeti.CStarAction

/-- Factor `f : A →⋆ₙₐ[ℂ] D` vanishing on `ker q` through a surjective `q : Hom α β`. -/
private def descendCoefficient {G A B D : Type*} [Group G] [TopologicalSpace G]
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
    {α : CStarAction G A} {β : CStarAction G B}
    (q : Hom α β) (hq : Function.Surjective q)
    (f : A →⋆ₙₐ[ℂ] D) (hf : ∀ a, q a = 0 → f a = 0) : B →⋆ₙₐ[ℂ] D :=
  (TwoSidedIdeal.Quotient.liftStarAlgHom (TwoSidedIdeal.ker q.toNonUnitalStarAlgHom) f
    fun a ha => hf a ((TwoSidedIdeal.mem_ker q.toNonUnitalStarAlgHom).mp ha)).comp
    (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
      (φ := q.toNonUnitalStarAlgHom) hq).symm.toNonUnitalStarAlgHom

private theorem descendCoefficient_apply {G A B D : Type*} [Group G] [TopologicalSpace G]
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
    {α : CStarAction G A} {β : CStarAction G B}
    (q : Hom α β) (hq : Function.Surjective q)
    (f : A →⋆ₙₐ[ℂ] D) (hf : ∀ a, q a = 0 → f a = 0) (a : A) :
    descendCoefficient q hq f hf (q a) = f a := by
  have hsymm :
      (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
        (φ := q.toNonUnitalStarAlgHom) hq).symm (q a) =
        TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker q.toNonUnitalStarAlgHom) a :=
    (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
      (φ := q.toNonUnitalStarAlgHom) hq).symm_apply_eq.mpr
      (NonUnitalStarAlgHom.quotientKerEquivOfSurjective_mk
        (φ := q.toNonUnitalStarAlgHom) hq a).symm
  simp [descendCoefficient, hsymm]

/-! ### Descent of Hilbert-space covariant representations -/

namespace CovariantRepresentation

section Basic

variable {G A B H : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B} (P : CovariantRepresentation α H)

/-- Descend a covariant representation `P` along a surjective equivariant homomorphism `q` whose
kernel is annihilated by `P.coefficient` to a covariant representation of `β` on `H`. -/
def descend (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → P.coefficient a = 0) : CovariantRepresentation β H where
  coefficient := descendCoefficient q hq P.coefficient hker
  group := P.group
  isUnitary := P.isUnitary
  continuous_orbit := P.continuous_orbit
  covariance r b ξ := by
    obtain ⟨a, rfl⟩ := hq b
    rw [← q.map_action, descendCoefficient_apply, descendCoefficient_apply]
    exact P.covariance r a ξ

/-- The descended coefficient representation sends `q a` to `P.coefficient a`. -/
@[simp]
theorem descend_coefficient_apply (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → P.coefficient a = 0) (a : A) :
    (P.descend q hq hker).coefficient (q a) = P.coefficient a :=
  descendCoefficient_apply q hq P.coefficient hker a

/-- Composing the descended coefficient representation with `q` recovers `P.coefficient`. -/
@[simp]
theorem descend_coefficient_comp (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → P.coefficient a = 0) :
    (P.descend q hq hker).coefficient.comp q.toNonUnitalStarAlgHom = P.coefficient :=
  NonUnitalStarAlgHom.ext (P.descend_coefficient_apply q hq hker)

/-- Descent preserves the unitary group representation identically. -/
@[simp]
theorem descend_group (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → P.coefficient a = 0) :
    (P.descend q hq hker).group = P.group :=
  (rfl)

/-- Pulling back `P.descend q hq hker` along `q` recovers `P`. -/
@[simp]
theorem comap_descend (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → P.coefficient a = 0) :
    (P.descend q hq hker).comap q = P :=
  CovariantRepresentation.ext
    ((comap_coefficient _ q).trans (P.descend_coefficient_comp q hq hker)) (comap_group _ q)

/-- Uniqueness of descent: `Q = P.descend q hq hker` if and only if `Q.comap q = P`. -/
theorem eq_descend_iff (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → P.coefficient a = 0) {Q : CovariantRepresentation β H} :
    Q = P.descend q hq hker ↔ Q.comap q = P := by
  refine ⟨fun h => h ▸ P.comap_descend q hq hker, fun hQ => ?_⟩
  refine CovariantRepresentation.ext (NonUnitalStarAlgHom.ext fun b => ?_)
    (by simpa using congrArg group hQ)
  obtain ⟨a, rfl⟩ := hq b
  simpa using DFunLike.congr_fun (congrArg coefficient hQ) a

/-- A covariant representation `P` of `α` is the pullback along a surjective `q : Hom α β` of some
covariant representation of `β` precisely when `P.coefficient` vanishes on `ker q`. -/
theorem exists_comap_eq_iff (q : Hom α β) (hq : Function.Surjective q) :
    (∃ Q : CovariantRepresentation β H, Q.comap q = P) ↔
      ∀ a, q a = 0 → P.coefficient a = 0 :=
  ⟨fun ⟨Q, hQ⟩ a ha => by
      have := DFunLike.congr_fun (congrArg coefficient hQ) a
      simpa [ha] using this.symm,
    fun hker => ⟨P.descend q hq hker, P.comap_descend q hq hker⟩⟩

/-- Descent along a surjective equivariant map preserves and reflects coefficient nondegeneracy. -/
@[simp]
theorem isNondegenerate_descend_coefficient_iff (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → P.coefficient a = 0) :
    (P.descend q hq hker).coefficient.IsNondegenerate ↔ P.coefficient.IsNondegenerate := by
  simp only [NonUnitalStarAlgHom.isNondegenerate_iff_dense,
    ← hq.iUnion_comp (fun b => Set.range ((P.descend q hq hker).coefficient b)),
    descend_coefficient_apply]

/-- Descend a covariant representation `P` vanishing on a closed `α`-invariant two-sided ideal `I`
to a covariant representation of the concrete quotient action `α.quotient I hI`. -/
def quotientLift (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) :
    CovariantRepresentation (α.quotient I hI) H :=
  P.descend (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI) fun a ha =>
    hP a (TwoSidedIdeal.Quotient.eq_zero_iff_mem.mp ((α.quotientMkHom_apply I hI a).symm.trans ha))

@[simp]
theorem quotientLift_coefficient_mk (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) (a : A) :
    (P.quotientLift I hI hP).coefficient (TwoSidedIdeal.Quotient.mk I a) = P.coefficient a := by
  rw [quotientLift, ← α.quotientMkHom_apply I hI, descend_coefficient_apply]

@[simp]
theorem quotientLift_group (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) :
    (P.quotientLift I hI hP).group = P.group :=
  (rfl)

@[simp]
theorem comap_quotientLift_quotientMkHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) :
    (P.quotientLift I hI hP).comap (α.quotientMkHom I hI) = P :=
  P.comap_descend (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI) _

/-- `Q = P.quotientLift I hI hP` if and only if pulling `Q` back along `α.quotientMkHom I hI`
recovers `P`. -/
theorem eq_quotientLift_iff (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) {Q : CovariantRepresentation (α.quotient I hI) H} :
    Q = P.quotientLift I hI hP ↔ Q.comap (α.quotientMkHom I hI) = P :=
  P.eq_descend_iff (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI) _

/-- `P` factors through `α.quotient I hI` precisely when `P.coefficient` vanishes on `I`. -/
theorem exists_comap_quotientMkHom_eq_iff (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    (∃ Q : CovariantRepresentation (α.quotient I hI) H, Q.comap (α.quotientMkHom I hI) = P) ↔
      ∀ a ∈ I, P.coefficient a = 0 := by
  rw [P.exists_comap_eq_iff (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI)]
  simp only [α.quotientMkHom_apply I hI, TwoSidedIdeal.Quotient.eq_zero_iff_mem]

@[simp]
theorem isNondegenerate_quotientLift_coefficient_iff (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) :
    (P.quotientLift I hI hP).coefficient.IsNondegenerate ↔ P.coefficient.IsNondegenerate :=
  P.isNondegenerate_descend_coefficient_iff (α.quotientMkHom I hI)
    (α.quotientMkHom_surjective I hI) _

end Basic

section Integration

variable {G A B H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B}
  (P : CovariantRepresentation α H) (q : Hom α β) (hq : Function.Surjective q)
  (hker : ∀ a, q a = 0 → P.coefficient a = 0) (μ : Measure G)

/-- Integrating `P.descend q hq hker` against `q.convolutionMap μ f` agrees with integrating `P`. -/
@[simp]
theorem integratedOperator_descend_convolutionMap
    [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ] (f : ConvolutionAlgebra α μ) :
    (P.descend q hq hker).integratedOperator μ (q.convolutionMap μ f).ofConv =
      P.integratedOperator μ f.ofConv := by
  rw [← (P.descend q hq hker).integratedOperator_comap q μ f, P.comap_descend q hq hker]

/-- Integrating `P.descend q hq hker` on the twisted L¹ completion agrees with integrating `P`
along `q.convolutionMapL1 μ`. -/
@[simp]
theorem integratedOperatorL1_descend_convolutionMapL1
    [BorelSpace G] [MeasurableMul G] [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (x : Completion (ConvolutionAlgebra α μ)) :
    (P.descend q hq hker).integratedOperatorL1 μ (q.convolutionMapL1 μ x) =
      P.integratedOperatorL1 μ x := by
  rw [← (P.descend q hq hker).integratedOperatorL1_comap q μ x, P.comap_descend q hq hker]

/-- Under a left Haar measure, `(P.descend q hq hker).integratedStarAlgHom μ` factors
`P.integratedStarAlgHom μ` through `q.convolutionMap μ`. -/
@[simp]
theorem integratedStarAlgHom_descend_comp_convolutionMap [BorelSpace G] [μ.IsHaarMeasure] :
    ((P.descend q hq hker).integratedStarAlgHom μ).comp (q.convolutionMap μ) =
      P.integratedStarAlgHom μ :=
  NonUnitalStarAlgHom.ext fun _ => by simp

theorem integratedStarAlgHom_descend_convolutionMap_apply [BorelSpace G] [μ.IsHaarMeasure]
    (f : ConvolutionAlgebra α μ) :
    (P.descend q hq hker).integratedStarAlgHom μ (q.convolutionMap μ f) =
      P.integratedStarAlgHom μ f :=
  DFunLike.congr_fun (P.integratedStarAlgHom_descend_comp_convolutionMap q hq hker μ) f

end Integration

end CovariantRepresentation

/-! ### Descent of multiplier-valued covariant homomorphisms -/

namespace CovariantMultiplierHom

section Basic

variable {G A B C D : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
  {α : CStarAction G A} {β : CStarAction G B} (M : CovariantMultiplierHom α C)

/-- Descend a multiplier-valued covariant homomorphism `M` along a surjective equivariant
homomorphism `q` whose kernel is annihilated by `M.coefficient`. -/
def descend (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → M.coefficient a = 0) : CovariantMultiplierHom β C where
  coefficient := descendCoefficient q hq M.coefficient hker
  group := M.group
  continuous_group_fst := M.continuous_group_fst
  covariance r b := by
    obtain ⟨a, rfl⟩ := hq b
    rw [← q.map_action, descendCoefficient_apply, descendCoefficient_apply]
    exact M.covariance r a

/-- The descended coefficient map sends `q a` to `M.coefficient a`. -/
@[simp]
theorem descend_coefficient_apply (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → M.coefficient a = 0) (a : A) :
    (M.descend q hq hker).coefficient (q a) = M.coefficient a :=
  descendCoefficient_apply q hq M.coefficient hker a

/-- Composing `(M.descend q hq hker).coefficient` with `q` recovers `M.coefficient`. -/
@[simp]
theorem descend_coefficient_comp (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → M.coefficient a = 0) :
    (M.descend q hq hker).coefficient.comp q.toNonUnitalStarAlgHom = M.coefficient :=
  NonUnitalStarAlgHom.ext (M.descend_coefficient_apply q hq hker)

/-- Descent preserves the unitary multiplier group homomorphism identically. -/
@[simp]
theorem descend_group (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → M.coefficient a = 0) :
    (M.descend q hq hker).group = M.group :=
  (rfl)

/-- Pulling back `M.descend q hq hker` along `q` recovers `M`. -/
@[simp]
theorem comap_descend (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → M.coefficient a = 0) :
    (M.descend q hq hker).comap q = M :=
  ext ((comap_coefficient _ q).trans (M.descend_coefficient_comp q hq hker)) (comap_group _ q)

/-- Uniqueness of descent: `N = M.descend q hq hker` if and only if `N.comap q = M`. -/
theorem eq_descend_iff (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → M.coefficient a = 0) {N : CovariantMultiplierHom β C} :
    N = M.descend q hq hker ↔ N.comap q = M := by
  refine ⟨fun h => h ▸ M.comap_descend q hq hker, fun hN => ?_⟩
  refine ext (NonUnitalStarAlgHom.ext fun b => ?_) (by simpa using congrArg group hN)
  obtain ⟨a, rfl⟩ := hq b
  simpa using DFunLike.congr_fun (congrArg coefficient hN) a

/-- A covariant multiplier homomorphism `M` of `α` factors through a surjective `q : Hom α β`
precisely when `M.coefficient` vanishes on `ker q`. -/
theorem exists_comap_eq_iff (q : Hom α β) (hq : Function.Surjective q) :
    (∃ N : CovariantMultiplierHom β C, N.comap q = M) ↔
      ∀ a, q a = 0 → M.coefficient a = 0 :=
  ⟨fun ⟨N, hN⟩ a ha => by
      have := DFunLike.congr_fun (congrArg coefficient hN) a
      simpa [ha] using this.symm,
    fun hker => ⟨M.descend q hq hker, M.comap_descend q hq hker⟩⟩

/-- Descent along a surjective equivariant map preserves and reflects multiplier nondegeneracy. -/
@[simp]
theorem isMultiplierNondegenerate_descend_coefficient_iff (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → M.coefficient a = 0) :
    (M.descend q hq hker).coefficient.IsMultiplierNondegenerate ↔
      M.coefficient.IsMultiplierNondegenerate := by
  rw [NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense_span_comp hq.denseRange]
  simp_rw [descend_coefficient_apply]
  exact NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense.symm

/-- Pushing forward along a nondegenerate multiplier homomorphism commutes with `descend`. -/
theorem map_descend (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → M.coefficient a = 0)
    {ψ : C →⋆ₙₐ[ℂ] 𝓜(ℂ, D)} (hψ : ψ.IsMultiplierNondegenerate) :
    (M.descend q hq hker).map hψ =
      (M.map hψ).descend q hq (fun a ha => by simp [hker a ha]) :=
  ((M.map hψ).eq_descend_iff q hq _).2 <| by rw [← map_comap, M.comap_descend]

/-- Extending to a Hilbert space via a nondegenerate representation commutes with `descend`. -/
theorem toCovariantRepresentation_descend (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → M.coefficient a = 0) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) :
    (M.descend q hq hker).toCovariantRepresentation hρ =
      (M.toCovariantRepresentation hρ).descend q hq (fun a ha => by simp [hker a ha]) :=
  ((M.toCovariantRepresentation hρ).eq_descend_iff q hq _).2 <| by
    rw [← toCovariantRepresentation_comap, M.comap_descend]

/-- Descend a covariant multiplier homomorphism `M` vanishing on a closed `α`-invariant two-sided
ideal `I` to the concrete quotient action `α.quotient I hI`. -/
def quotientLift (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hM : ∀ a ∈ I, M.coefficient a = 0) :
    CovariantMultiplierHom (α.quotient I hI) C :=
  M.descend (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI) fun a ha =>
    hM a (TwoSidedIdeal.Quotient.eq_zero_iff_mem.mp ((α.quotientMkHom_apply I hI a).symm.trans ha))

@[simp]
theorem quotientLift_coefficient_mk (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hM : ∀ a ∈ I, M.coefficient a = 0) (a : A) :
    (M.quotientLift I hI hM).coefficient (TwoSidedIdeal.Quotient.mk I a) = M.coefficient a := by
  rw [quotientLift, ← α.quotientMkHom_apply I hI, descend_coefficient_apply]

@[simp]
theorem quotientLift_group (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hM : ∀ a ∈ I, M.coefficient a = 0) :
    (M.quotientLift I hI hM).group = M.group :=
  (rfl)

@[simp]
theorem comap_quotientLift_quotientMkHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hM : ∀ a ∈ I, M.coefficient a = 0) :
    (M.quotientLift I hI hM).comap (α.quotientMkHom I hI) = M :=
  M.comap_descend (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI) _

/-- `N = M.quotientLift I hI hM` if and only if pulling `N` back along `α.quotientMkHom I hI`
recovers `M`. -/
theorem eq_quotientLift_iff (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hM : ∀ a ∈ I, M.coefficient a = 0) {N : CovariantMultiplierHom (α.quotient I hI) C} :
    N = M.quotientLift I hI hM ↔ N.comap (α.quotientMkHom I hI) = M :=
  M.eq_descend_iff (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI) _

/-- `M` factors through `α.quotient I hI` precisely when `M.coefficient` vanishes on `I`. -/
theorem exists_comap_quotientMkHom_eq_iff (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    (∃ N : CovariantMultiplierHom (α.quotient I hI) C, N.comap (α.quotientMkHom I hI) = M) ↔
      ∀ a ∈ I, M.coefficient a = 0 := by
  rw [M.exists_comap_eq_iff (α.quotientMkHom I hI) (α.quotientMkHom_surjective I hI)]
  simp only [α.quotientMkHom_apply I hI, TwoSidedIdeal.Quotient.eq_zero_iff_mem]

@[simp]
theorem isMultiplierNondegenerate_quotientLift_coefficient_iff (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hM : ∀ a ∈ I, M.coefficient a = 0) :
    (M.quotientLift I hI hM).coefficient.IsMultiplierNondegenerate ↔
      M.coefficient.IsMultiplierNondegenerate :=
  M.isMultiplierNondegenerate_descend_coefficient_iff (α.quotientMkHom I hI)
    (α.quotientMkHom_surjective I hI) _

end Basic

section Integration

variable {G A B C : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} {β : CStarAction G B}
  (M : CovariantMultiplierHom α C) (q : Hom α β) (hq : Function.Surjective q)
  (hker : ∀ a, q a = 0 → M.coefficient a = 0) (μ : Measure G)

/-- Strict Bochner integration of `M.descend q hq hker` on `q.convolutionMap μ f` agrees with
integrating `M` on `f`. -/
@[simp]
theorem integratedMultiplier_descend_convolutionMap
    [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ] (f : ConvolutionAlgebra α μ) :
    (M.descend q hq hker).integratedMultiplier μ (q.convolutionMap μ f).ofConv =
      M.integratedMultiplier μ f.ofConv := by
  rw [← (M.descend q hq hker).integratedMultiplier_comap μ q f, M.comap_descend q hq hker]

/-- Under a left Haar measure, `(M.descend q hq hker).integratedStarAlgHom μ` factors
`M.integratedStarAlgHom μ` through `q.convolutionMap μ`. -/
@[simp]
theorem integratedStarAlgHom_descend_comp_convolutionMap [BorelSpace G] [μ.IsHaarMeasure] :
    ((M.descend q hq hker).integratedStarAlgHom μ).comp (q.convolutionMap μ) =
      M.integratedStarAlgHom μ := by
  rw [← (M.descend q hq hker).integratedStarAlgHom_comap μ q, M.comap_descend q hq hker]

theorem integratedStarAlgHom_descend_convolutionMap_apply [BorelSpace G] [μ.IsHaarMeasure]
    (f : ConvolutionAlgebra α μ) :
    (M.descend q hq hker).integratedStarAlgHom μ (q.convolutionMap μ f) =
      M.integratedStarAlgHom μ f :=
  DFunLike.congr_fun (M.integratedStarAlgHom_descend_comp_convolutionMap q hq hker μ) f

end Integration

end CovariantMultiplierHom

end TauCeti.CStarAction
