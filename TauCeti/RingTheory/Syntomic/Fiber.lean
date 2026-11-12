/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RingHom.StandardSyntomic
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.RingTheory.Extension.Presentation.Fiber
import TauCeti.RingTheory.KrullDimension.Presentation

/-!
# The fibrewise criterion for syntomic ring maps

A flat, finitely presented `R`-algebra `A` whose fibres `κ(p) ⊗[R] A` are all locally standard
syntomic of relative dimension `n` over the residue fields `κ(p)` is itself locally standard
syntomic of relative dimension `n` over `R`
(`TauCeti.locally_isStandardSyntomicOfRelativeDimension_of_fiber`). This is the affine form of the
statement that a flat, locally finitely presented morphism with syntomic fibres of relative
dimension `n` is syntomic of relative dimension `n`.

Let `q` be a prime of `A` over `p`. A standard syntomic chart `(κ(p) ⊗[R] A)[1/t]` of the fibre
around `q` lifts, up to a unit of `κ(p)`, to an element `a ∉ q` of `A` whose fibre
`κ(p) ⊗[R] A[1/a]` is that chart. Its complete-intersection presentation then lifts to a
presentation of some localization `A[1/a][1/g]` with `n + c` generators and `c` relations
(`Algebra.Presentation.exists_presentation_localizationAway_of_fiber`). The fibres of this
localization have Krull dimension at least `n` by Krull's height theorem applied to the base
changed presentation, and at most `n` because they are again locally standard syntomic of
relative dimension `n` over a field
(`TauCeti.ringKrullDim_le_of_locally_isStandardSyntomicOfRelativeDimension`).

## Main results

* `TauCeti.ringKrullDim_le_of_locally_isStandardSyntomicOfRelativeDimension`: an algebra over a
  field which is locally standard syntomic of relative dimension `n` has Krull dimension at most
  `n`.
* `TauCeti.exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away`: under the
  fibrewise hypothesis, every prime `q` of `A` has a standard syntomic neighbourhood `A[1/g]` of
  relative dimension `n` with `g ∉ q`.
* `TauCeti.locally_isStandardSyntomicOfRelativeDimension_of_fiber`: the fibrewise criterion.

## References

* The Stacks Project, Commutative Algebra, Section *Syntomic morphisms*: a flat finitely presented
  ring map whose fibre is a local complete intersection at a prime is a relative global complete
  intersection near that prime.
-/

public section

open TensorProduct

namespace TauCeti

universe u

variable {n : ℕ}

/-- An algebra over a field which is locally standard syntomic of relative dimension `n` has Krull
dimension at most `n`. -/
theorem ringKrullDim_le_of_locally_isStandardSyntomicOfRelativeDimension {k A : Type u} [Field k]
    [CommRing A] [Algebra k A]
    (h : RingHom.Locally (IsStandardSyntomicOfRelativeDimension n) (algebraMap k A)) :
    ringKrullDim A ≤ n := by
  obtain ⟨s, hs, hst⟩ := h
  refine (ringKrullDim_le_iff_height_le _).mpr fun P hP ↦ ?_
  -- Some chart `A[1/t]` of the cover contains `P`, and the height of `P` is computed there.
  obtain ⟨t, hts, hdisj⟩ := Ideal.exists_disjoint_powers_of_span_eq_top s hs P hP.ne_top
  have hPt : (P.map (algebraMap A (Localization.Away t))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ P hP hdisj.symm
  have : Algebra.IsStandardSyntomicOfRelativeDimension n k (Localization.Away t) := by
    rw [← isStandardSyntomicOfRelativeDimension_algebraMap, IsScalarTower.algebraMap_eq k A]
    exact hst t hts
  -- The chart is nonzero, so over the field `k` its Krull dimension is exactly `n`.
  let e := Algebra.TensorProduct.lid k (Localization.Away t)
  have : Nontrivial (Localization.Away t) := nontrivial_of_ne 0 1 fun h ↦
    hPt.ne_top ((Ideal.eq_top_iff_one _).mpr (h ▸ Ideal.zero_mem _))
  have : Nontrivial (k ⊗[k] Localization.Away t) := e.toEquiv.nontrivial
  rw [← IsLocalization.height_map_of_disjoint (S := Localization.Away t) (.powers t) P
    hdisj.symm]
  refine Ideal.height_le_ringKrullDim_of_isPrime.trans_eq ?_
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
    Algebra.IsStandardSyntomicOfRelativeDimension.ringKrullDim_tensorProduct_of_field (n := n) k]

/-- If every fibre of `A` is locally standard syntomic of relative dimension `n`, so is every fibre
of a localization `B = A[1/a]`, since `κ(p) ⊗[R] A[1/a]` is the localization of `κ(p) ⊗[R] A`
away from `1 ⊗ a`. -/
private theorem locally_fiber_of_isLocalization_away {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (a : A) (B : Type u) [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [IsLocalization.Away a B] (p : Ideal R) [p.IsPrime]
    (h : RingHom.Locally (IsStandardSyntomicOfRelativeDimension n)
      (algebraMap p.ResidueField (p.Fiber A))) :
    RingHom.Locally (IsStandardSyntomicOfRelativeDimension n)
      (algebraMap p.ResidueField (p.Fiber B)) := by
  have hloc := locally_isStandardSyntomicOfRelativeDimension_propertyIsLocal n
  let e := IsLocalization.Away.tensorProductEquivTMulRight R p.ResidueField a B
  have h' := hloc.StableUnderCompositionWithLocalizationAwayTarget
    (Localization.Away ((1 : p.ResidueField) ⊗ₜ[R] a)) ((1 : p.ResidueField) ⊗ₜ[R] a) _ h
  rw [← IsScalarTower.algebraMap_eq] at h'
  have he : e.symm.toRingEquiv.toRingHom.comp (algebraMap p.ResidueField _) =
      algebraMap p.ResidueField (p.Fiber B) :=
    RingHom.ext e.symm.commutes
  exact he ▸ hloc.respectsIso.left _ e.symm.toRingEquiv h'

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- A standard syntomic chart of the fibre `κ(p) ⊗[R] A` around a prime `q` of `A` over `p` is, up
to isomorphism, the fibre `κ(p) ⊗[R] A[1/a]` of a localization of `A` away from some `a ∉ q`. -/
private theorem exists_notMem_isStandardSyntomicOfRelativeDimension_fiber_localization_away
    {p : Ideal R} [p.IsPrime]
    (h : RingHom.Locally (IsStandardSyntomicOfRelativeDimension n)
      (algebraMap p.ResidueField (p.Fiber A)))
    (q : Ideal A) [q.IsPrime] [q.LiesOver p] :
    ∃ a ∉ q, Algebra.IsStandardSyntomicOfRelativeDimension n p.ResidueField
      (p.Fiber (Localization.Away a)) := by
  -- The point of the fibre `Spec (κ(p) ⊗[R] A)` corresponding to `q`.
  let Q := PrimeSpectrum.primesOverOrderIsoFiber R A p ⟨q, inferInstance, inferInstance⟩
  have hQ : Q.asIdeal.comap Algebra.TensorProduct.includeRight = q := by
    rw [← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply, OrderIso.symm_apply_apply]
  -- Choose a standard syntomic chart `(κ(p) ⊗[R] A)[1/t]` of the fibre around `Q`.
  obtain ⟨s, hs, hst⟩ := h
  obtain ⟨t, hts, hdisj⟩ := Ideal.exists_disjoint_powers_of_span_eq_top s hs _ Q.isPrime.ne_top
  have htQ : t ∉ Q.asIdeal :=
    (Ideal.disjoint_powers_iff_notMem t Q.isPrime.isRadical).mp hdisj.symm
  -- Up to a unit of `κ(p)`, `t` is the image `1 ⊗ a` of some `a ∉ q`.
  obtain ⟨r, hr, a, hra⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p t
  have hunit : IsUnit (algebraMap R (p.Fiber A) r) := by
    rw [IsScalarTower.algebraMap_apply R p.ResidueField]
    refine (IsUnit.mk0 _ fun h0 ↦ hr ?_).map _
    rwa [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField] at h0
  have hta : Associated t ((1 : p.ResidueField) ⊗ₜ[R] a) :=
    ⟨hunit.unit, by rw [IsUnit.unit_spec, mul_comm, ← Algebra.smul_def, hra]⟩
  refine ⟨a, ?_, ?_⟩
  · rw [← hQ, Ideal.mem_comap, Algebra.TensorProduct.includeRight_apply, ← hra, Algebra.smul_def,
      Ideal.unit_mul_mem_iff_mem _ hunit]
    exact htQ
  -- The fibre of `A[1/a]` at `p` is the chart `(κ(p) ⊗[R] A)[1/t]`.
  have : IsLocalization.Away ((1 : p.ResidueField) ⊗ₜ[R] a) (Localization.Away t) :=
    IsLocalization.Away.of_associated hta
  let e : p.Fiber (Localization.Away a) ≃ₐ[p.ResidueField] Localization.Away t :=
    (IsLocalization.Away.tensorProductEquivTMulRight R p.ResidueField a _).trans
      ((IsLocalization.algEquiv (.powers ((1 : p.ResidueField) ⊗ₜ[R] a)) _ _).restrictScalars _)
  have : Algebra.IsStandardSyntomicOfRelativeDimension n p.ResidueField (Localization.Away t) := by
    rw [← isStandardSyntomicOfRelativeDimension_algebraMap,
      IsScalarTower.algebraMap_eq p.ResidueField (p.Fiber A)]
    exact hst t hts
  exact .of_algEquiv e.symm

/-- A flat `R`-algebra `B` with a presentation by `n + c` generators and `c` relations, all of
whose fibres are locally standard syntomic of relative dimension `n`, is standard syntomic of
relative dimension `n`: its nonzero fibres have Krull dimension at most `n` because they are
locally standard syntomic, and at least `n` by Krull's height theorem. -/
private theorem isStandardSyntomicOfRelativeDimension_of_presentation {B : Type u} [CommRing B]
    [Algebra R B] [Module.Flat R B] {ι σ : Type} [Finite ι] [Finite σ]
    (P : Algebra.Presentation R B ι σ) (hP : Nat.card ι = n + Nat.card σ)
    (h : ∀ (p : Ideal R) [p.IsPrime], RingHom.Locally (IsStandardSyntomicOfRelativeDimension n)
      (algebraMap p.ResidueField (p.Fiber B))) :
    Algebra.IsStandardSyntomicOfRelativeDimension n R B := by
  refine P.isStandardSyntomicOfRelativeDimension hP fun p _ _ ↦ le_antisymm
    (ringKrullDim_le_of_locally_isStandardSyntomicOfRelativeDimension (h p)) ?_
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (p.Fiber B)
  have hdim : (P.baseChange p.ResidueField).dimension = n := by
    simp [Algebra.Presentation.dimension, hP]
  have h₁ := (P.baseChange p.ResidueField).dimension_le_height_of_isMaximal m
  rw [hdim] at h₁
  exact (WithBot.coe_le_coe.mpr h₁).trans Ideal.height_le_ringKrullDim_of_isPrime

/-- Let `A` be a flat, finitely presented `R`-algebra all of whose fibres `κ(p) ⊗[R] A` are locally
standard syntomic of relative dimension `n` over `κ(p)`. Then every prime `q` of `A` has a
neighbourhood `A[1/g]`, `g ∉ q`, which is standard syntomic of relative dimension `n` over `R`. -/
theorem exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away [Module.Flat R A]
    [Algebra.FinitePresentation R A]
    (h : ∀ (p : Ideal R) [p.IsPrime], RingHom.Locally (IsStandardSyntomicOfRelativeDimension n)
      (algebraMap p.ResidueField (p.Fiber A)))
    (q : Ideal A) [q.IsPrime] :
    ∃ g ∉ q, Algebra.IsStandardSyntomicOfRelativeDimension n R (Localization.Away g) := by
  let p := q.comap (algebraMap R A)
  have : q.LiesOver p := ⟨rfl⟩
  -- A neighbourhood `A' = A[1/a]` of `q` whose fibre at `p` has a presentation over `κ(p)` with
  -- `n + c` generators and `c` relations.
  obtain ⟨a, haq, hfib⟩ :=
    exists_notMem_isStandardSyntomicOfRelativeDimension_fiber_localization_away (h p) q
  obtain ⟨ι, σ, _, _, P, hP⟩ := hfib.exists_presentation
  let A' := Localization.Away a
  -- Lift that presentation to a neighbourhood `B = A'[1/g']` of the prime `q A'`.
  let q' := q.map (algebraMap A A')
  have hdisj : Disjoint (Submonoid.powers a : Set A) q :=
    (Ideal.disjoint_powers_iff_notMem a ‹q.IsPrime›.isRadical).mpr haq
  have : q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ q inferInstance hdisj
  have hq' : q'.comap (algebraMap A A') = q :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ inferInstance hdisj
  have : q'.LiesOver q := ⟨hq'.symm⟩
  have : q'.LiesOver p := .trans q' q p
  obtain ⟨g', hg'q, ι', σ', _, _, P', hP'⟩ :=
    Algebra.Presentation.exists_presentation_localizationAway_of_fiber P hP q'
  let B := Localization.Away g'
  have : Module.Flat R B := .trans R A' B
  have hB : Algebra.IsStandardSyntomicOfRelativeDimension n R B :=
    isStandardSyntomicOfRelativeDimension_of_presentation P' hP' fun p₁ _ ↦
      locally_fiber_of_isLocalization_away g' B p₁
        (locally_fiber_of_isLocalization_away a A' p₁ (h p₁))
  -- Finally `B` is the localization of `A` away from `a * g₀`, where `g'` and `g₀` are associated.
  obtain ⟨k, g₀, hg₀⟩ := IsLocalization.Away.surj a g'
  have hg₀' : Associated (algebraMap A A' g₀) g' :=
    ⟨((IsLocalization.Away.algebraMap_isUnit a).pow k).unit⁻¹, by
      rw [Units.mul_inv_eq_iff_eq_mul, IsUnit.unit_spec, hg₀]⟩
  have : IsLocalization.Away (a * g₀) B := IsLocalization.Away.mul_of_associated a g₀ g' hg₀'
  have hg₀q : g₀ ∉ q := by
    rw [← hq', Ideal.mem_comap, ← hg₀,
      Ideal.mul_unit_mem_iff_mem _ ((IsLocalization.Away.algebraMap_isUnit a).pow k)]
    exact hg'q
  refine ⟨a * g₀, fun hmem ↦ ?_, hB.of_algEquiv
    ((IsLocalization.algEquiv (.powers (a * g₀)) B (Localization.Away (a * g₀))).restrictScalars R)⟩
  rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h' | h'
  · exact haq h'
  · exact hg₀q h'

/-- **The fibrewise criterion for syntomic ring maps.** A flat, finitely presented `R`-algebra `A`
whose fibres `κ(p) ⊗[R] A` are all locally standard syntomic of relative dimension `n` over `κ(p)`
is locally standard syntomic of relative dimension `n` over `R`. -/
theorem locally_isStandardSyntomicOfRelativeDimension_of_fiber [Module.Flat R A]
    [Algebra.FinitePresentation R A]
    (h : ∀ (p : Ideal R) [p.IsPrime], RingHom.Locally (IsStandardSyntomicOfRelativeDimension n)
      (algebraMap p.ResidueField (p.Fiber A))) :
    RingHom.Locally (IsStandardSyntomicOfRelativeDimension n) (algebraMap R A) := by
  rw [RingHom.locally_iff_span_eq_top]
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨g, hg, hstd⟩ := exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away h m
  refine hg (hle (Ideal.subset_span ?_))
  rw [Set.mem_ofPred_eq, ← IsScalarTower.algebraMap_eq,
    isStandardSyntomicOfRelativeDimension_algebraMap]
  exact hstd

end TauCeti
