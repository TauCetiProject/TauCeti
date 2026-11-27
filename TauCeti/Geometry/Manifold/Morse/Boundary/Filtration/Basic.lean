/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject

/-!
# The critical-value filtration of a Morse complex

Let `f` be a function with finitely many critical points. A Morse complex of `f` is built from a
matrix of coefficients `coeff p q` between its critical points, the coefficient of `q` in the
boundary of `p`, which lowers the Morse index by one, strictly lowers the critical value and
squares to zero (`TauCeti.MorseBoundaryCoeffs`). The trajectories of a Morse–Smale pseudo-gradient
give such coefficients, counted modulo two
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundaryCoeffs`,
in `TauCeti.Geometry.Manifold.Morse.Boundary.Filtration.ModTwo`) or with their signs over a ring in
which the integral Morse boundary squares to zero
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeffs`,
in `TauCeti.Geometry.Manifold.Morse.Boundary.Filtration.Integral`). Since the boundary of a
critical point `p` only involves critical points of smaller critical value, the Morse complex is
filtered by critical values. This file constructs this filtration and studies its spectral
sequence, for any such coefficients.

* **Morse chains with values in a set.** For an order-connected set `s` of real numbers, the
  critical points with critical value in `s` span a complex
  (`TauCeti.MorseBoundaryCoeffs.complexOn`): its term in degree `n` is the free `R`-module on the
  critical points of index `n` with value in `s` (`TauCeti.MorseGenerators`), and its
  differential is given by the coefficients between them. The differential squares to zero
  because a composite `p → q → r` of nonzero coefficients has `f r < f q < f p`, so `q` has its
  value in `s` whenever `p` and `r` do. For `s = univ` this is the whole Morse complex.
* **Sublevels and bands.** For `a ≤ b`, the chains of the sublevel `Iic a` form a subcomplex of
  those of `Iic b`, and the quotient is the complex of the band `Ioc a b`: the sequence
  `0 → C(Iic a) → C(Iic b) → C(Ioc a b) → 0` is a short exact sequence of complexes
  (`TauCeti.MorseBoundaryCoeffs.bandSequence_shortExact`). When all critical values in the band
  agree, the band complex has zero differential, so its homology in degree `n` is the free module
  on the critical points of index `n` in the band.
* **The critical-value spectral sequence.** For a monotone sequence `a : ℤ → ℝ` of cut values, the
  sublevel complexes of the `a q` form an increasing filtration of the Morse complex
  (`TauCeti.MorseBoundaryCoeffs.filtration`), regraded as a cochain complex in nonpositive degrees
  along `n ↦ -n`. Its spectral sequence (`TauCeti.MorseBoundaryCoeffs.spectralSequence`) has on
  its first page (numbered `2` in the indexing of `CochainComplex.spectralSequence`), at `(p, q)`
  with `p + q = -n`, the homology in degree `n` of the band `Ioc (a q) (a (q + 1))`
  (`TauCeti.MorseBoundaryCoeffs.spectralSequenceFirstPageXIso`). If each band contains at most
  one critical value, this is the free `R`-module on the critical points of index `n` in the band
  (`TauCeti.MorseBoundaryCoeffs.spectralSequenceFirstPageXIsoOfSubsingleton`). If some `a q` lies
  below and some `a q'` above all critical values, the filtration is finite and the spectral
  sequence converges strongly to the Morse homology: on every late enough page the object at
  `(p, q)` is the graded piece of the induced filtration of the Morse homology in degree
  `-(p + q)` (`TauCeti.MorseBoundaryCoeffs.spectralSequencePageXIsoGraded`, with abutment
  `TauCeti.MorseBoundaryCoeffs.filtrationAbutmentIso`).

The singular counterpart, the spectral sequence of the filtration of `M` by the sublevels
`{f ≤ a q}`, is `TauCeti.Geometry.Manifold.Morse.SpectralSequence`. For a critical-band cut its
first page is also free on the critical points in each band; comparing the two spectral sequences
through a filtered chain map is not attempted here. The regrading of the filtration and the
identification of its graded pieces and abutment follow the singular construction
`TauCeti.chainFiltration` in `TauCeti.AlgebraicTopology.Singular.FilteredSpace.ChainFunctor`.

## Main declarations

* `TauCeti.MorseBoundaryCoeffs`: coefficients of a Morse boundary lowering the index by one and
  the critical value strictly, and squaring to zero.

In the namespace `TauCeti.MorseBoundaryCoeffs`:

* `complexOn`: the Morse complex of the critical points with value in `s`.
* `complexOnInclusion`, `complexOnRestriction`: the chain maps between these complexes for a lower
  and for an upper part of `s`.
* `complexOn_d_eq_zero`: with at most one critical value in `s`, the differential vanishes.
* `complexOnUnivIso`: the Morse complex with all critical values is the chain complex on the
  critical points of each index with any differentials given by the coefficients.
* `bandSequence_shortExact`: the short exact sequence of a sublevel, a larger sublevel and the
  band between them.
* `filtration`: the critical-value filtration of the regraded Morse complex.
* `spectralSequence`: its spectral sequence.
* `spectralSequenceFirstPageXIso`, `spectralSequenceFirstPageXIsoOfSubsingleton`,
  `finrank_spectralSequence_page_two_X`: its first page.
* `filtrationAbutmentIso`, `filtrationAbutmentIsoOfIso`, `spectralSequencePageXIsoGraded`: its
  convergence to Morse homology.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.4 (the filtration of the Morse complex by critical values
  and its spectral sequence).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2 (the spectral sequence of a filtered complex).
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

variable (E f) in
/-- The critical points of `f` of Morse index `n` whose critical value lies in `s`: the generators
in degree `n` of the Morse chains with critical values in `s`. -/
abbrev MorseGenerators (n : ℕ) (s : Set ℝ) : Type _ :=
  {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n ∧ f p ∈ s}

namespace MorseGenerators

/-- For `s ⊆ t`, a critical point with value in `s` is one with value in `t`. -/
def inclusion {n : ℕ} {s t : Set ℝ} (hst : s ⊆ t) (p : MorseGenerators E f n s) :
    MorseGenerators E f n t :=
  ⟨p.val, p.property.1, hst p.property.2⟩

@[simp]
theorem coe_inclusion {n : ℕ} {s t : Set ℝ} (hst : s ⊆ t) (p : MorseGenerators E f n s) :
    (inclusion hst p).val = p.val :=
  (rfl)

theorem inclusion_injective {n : ℕ} {s t : Set ℝ} (hst : s ⊆ t) :
    Function.Injective (inclusion (E := E) (f := f) (n := n) hst) :=
  fun _ _ he ↦ Subtype.ext (congrArg (fun p : MorseGenerators E f n t ↦ p.val) he)

@[simp]
theorem inclusion_inclusion {n : ℕ} {s t u : Set ℝ} (hst : s ⊆ t) (htu : t ⊆ u)
    (p : MorseGenerators E f n s) :
    inclusion htu (inclusion hst p) = inclusion (hst.trans htu) p :=
  (rfl)

/-- A critical point with value in `t` comes from `s ⊆ t` exactly when its value lies in `s`. -/
theorem mem_range_inclusion_iff {n : ℕ} {s t : Set ℝ} (hst : s ⊆ t) (q : MorseGenerators E f n t) :
    q ∈ Set.range (inclusion hst) ↔ f q.val ∈ s :=
  ⟨fun ⟨p, hp⟩ ↦ hp ▸ p.property.2, fun hq ↦ ⟨⟨q.val, q.property.1, hq⟩, rfl⟩⟩

variable (E f) in
/-- The critical points of index `n` with value anywhere are the critical points of index `n`. -/
def univEquiv (n : ℕ) :
    MorseGenerators E f n univ ≃
      {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} :=
  Equiv.subtypeEquivRight fun _ ↦ and_iff_left (mem_univ _)

@[simp]
theorem coe_univEquiv_apply {n : ℕ} (p : MorseGenerators E f n univ) :
    (univEquiv E f n p).val = p.val :=
  (rfl)

@[simp]
theorem coe_univEquiv_symm_apply {n : ℕ}
    (p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n}) :
    ((univEquiv E f n).symm p).val = p.val :=
  (rfl)

end MorseGenerators

variable (E f) in
/-- **A boundary coefficient system** for `f` with coefficients in a ring `R`: a matrix of
coefficients `coeff p q` between the critical points of `f`, of which there are finitely many,
that lowers the Morse index by one, strictly lowers the critical value, and squares to zero. The
mod-two counts of trajectories of a Morse–Smale pseudo-gradient form one
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundaryCoeffs`), and so do the integral
boundary coefficients `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff` (the signed
counts of trajectories when the pseudo-gradient is Morse–Smale), with coefficients in any ring in
which the integral Morse boundary squares to zero
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeffs`). -/
@[ext]
structure MorseBoundaryCoeffs (R : Type*) [Ring R] where
  /-- The coefficient of the critical point `q` in the boundary of the critical point `p`. -/
  coeff : criticalPoints 𝓘(ℝ, E) f → criticalPoints 𝓘(ℝ, E) f → R
  /-- There are finitely many critical points. -/
  finite_criticalPoints : (criticalPoints 𝓘(ℝ, E) f).Finite
  /-- A nonzero coefficient joins critical points whose indices differ by one. -/
  morseIndex_eq_add_one_of_coeff_ne_zero {p q : criticalPoints 𝓘(ℝ, E) f} :
    coeff p q ≠ 0 → manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  /-- A nonzero coefficient joins critical points with strictly decreasing critical value. -/
  value_lt_of_coeff_ne_zero {p q : criticalPoints 𝓘(ℝ, E) f} : coeff p q ≠ 0 → f q < f p
  /-- The boundary squares to zero. -/
  finsum_coeff_mul_coeff (p r : criticalPoints 𝓘(ℝ, E) f) : ∑ᶠ q, coeff p q * coeff q r = 0

namespace MorseBoundaryCoeffs

variable {R : Type*} [Ring R] (C : MorseBoundaryCoeffs E f R)

/-- The coefficient of `q` in the boundary of `p` vanishes unless the critical value drops. -/
theorem coeff_eq_zero_of_value_le {p q : criticalPoints 𝓘(ℝ, E) f} (hpq : f p ≤ f q) :
    C.coeff p q = 0 := by
  by_contra hne
  exact (C.value_lt_of_coeff_ne_zero hne).not_ge hpq

/-- The boundary squares to zero, as a sum over the finitely many critical points. -/
theorem sum_coeff_mul_coeff [Fintype (criticalPoints 𝓘(ℝ, E) f)]
    (p r : criticalPoints 𝓘(ℝ, E) f) : ∑ q, C.coeff p q * C.coeff q r = 0 := by
  rw [← finsum_eq_sum_of_fintype]
  exact C.finsum_coeff_mul_coeff p r

include C in
/-- There are finitely many critical points of each index with value in a given set. -/
theorem finite_morseGenerators (n : ℕ) (s : Set ℝ) : Finite (MorseGenerators E f n s) :=
  haveI := C.finite_criticalPoints.to_subtype
  inferInstance

/-! ### Morse chains with critical values in a set -/

/-- **The Morse boundary with critical values in `s`.** The `R`-linear map from the free
module on the critical points of index `n + 1` with value in `s` to the free module on those of
index `n`, sending `p` to the sum of the critical points `q`, each weighted by the coefficient
`C.coeff p q`. -/
def boundaryOn (s : Set ℝ) (n : ℕ) :
    (MorseGenerators E f (n + 1) s →₀ R) →ₗ[R] (MorseGenerators E f n s →₀ R) :=
  haveI := C.finite_morseGenerators n s
  Finsupp.linearCombination R fun p ↦
    Finsupp.ofSupportFinite (fun q ↦ C.coeff p.val q.val) (toFinite _)

/-- The coefficient of `q` in the Morse boundary with values in `s` of a chain `c` is the sum over
the critical points `p` of `c p` times the coefficient `C.coeff p q`. -/
theorem boundaryOn_apply {s : Set ℝ} {n : ℕ} (c : MorseGenerators E f (n + 1) s →₀ R)
    (q : MorseGenerators E f n s) :
    C.boundaryOn s n c q = c.sum fun p a ↦ a * C.coeff p.val q.val := by
  simp [boundaryOn, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

/-- The coefficient of `q` in the Morse boundary with values in `s` of `a • p` is `a` times the
coefficient `C.coeff p q`. -/
@[simp]
theorem boundaryOn_single_apply {s : Set ℝ} {n : ℕ} (p : MorseGenerators E f (n + 1) s)
    (a : R) (q : MorseGenerators E f n s) :
    C.boundaryOn s n (Finsupp.single p a) q = a * C.coeff p.val q.val := by
  rw [boundaryOn_apply, Finsupp.sum_single_index (zero_mul _)]

/-- The Morse boundary with values in `s` as a sum over all critical points of index `n + 1` with
value in `s`. -/
private theorem boundaryOn_apply_eq_sum {s : Set ℝ} {n : ℕ}
    [Fintype (MorseGenerators E f (n + 1) s)] (c : MorseGenerators E f (n + 1) s →₀ R)
    (q : MorseGenerators E f n s) :
    C.boundaryOn s n c q = ∑ p, c p * C.coeff p.val q.val := by
  rw [boundaryOn_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]

/-- **The Morse boundary with values in an order-connected set squares to zero.** A composite
`p → q → r` of nonzero coefficients has `f r < f q < f p`, so if the values of `p` and `r` lie in
the order-connected set `s`, so does that of `q`. -/
@[simp]
theorem boundaryOn_comp_boundaryOn (s : Set ℝ) [s.OrdConnected] (n : ℕ) :
    C.boundaryOn s n ∘ₗ C.boundaryOn s (n + 1) = 0 := by
  classical
  have := C.finite_criticalPoints.to_subtype
  let _ := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  let _ := Fintype.ofFinite (MorseGenerators E f (n + 1) s)
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
  rw [LinearMap.comp_apply, boundaryOn_apply_eq_sum, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  simp only [boundaryOn_single_apply, mul_assoc, ← Finset.mul_sum]
  refine mul_eq_zero_of_right _ ?_
  rw [← C.sum_coeff_mul_coeff p.val r.val]
  refine Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
    (fun q hq ↦ ?_) fun _ ↦ rfl
  -- A critical point outside the generators contributes nothing.
  by_contra hne
  have h₁ : C.coeff p.val q ≠ 0 := left_ne_zero_of_mul hne
  have h₂ : C.coeff q r.val ≠ 0 := right_ne_zero_of_mul hne
  refine hq ⟨⟨q, ?_, Set.OrdConnected.out ‹_› r.property.2 p.property.2
    ⟨(C.value_lt_of_coeff_ne_zero h₂).le,
      (C.value_lt_of_coeff_ne_zero h₁).le⟩⟩, rfl⟩
  have := C.morseIndex_eq_add_one_of_coeff_ne_zero h₁
  have := p.property.1
  omega

/-- **The Morse complex with critical values in `s`.** For an order-connected set `s`, the chain
complex of `R`-modules whose term in degree `n` is the free module on the critical points of index
`n` with critical value in `s`, with the differential given by the coefficients `C.coeff`. For
`s = univ` it is the whole Morse complex. -/
-- The body is exposed so that the terms of the complex compute to the free modules on the
-- critical points, which the statements of `complexOn_X` and `complexOn_d` need.
@[expose]
def complexOn (s : Set ℝ) [s.OrdConnected] : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (MorseGenerators E f n s →₀ R))
    (fun n ↦ ModuleCat.ofHom (C.boundaryOn s n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, C.boundaryOn_comp_boundaryOn, ModuleCat.ofHom_zero]

variable (s t u : Set ℝ) [s.OrdConnected] [t.OrdConnected] [u.OrdConnected]

/-- The term of the Morse complex with values in `s` in degree `n` is the free `R`-module on
the critical points of index `n` with value in `s`. -/
@[simp]
theorem complexOn_X (n : ℕ) :
    (C.complexOn s).X n = ModuleCat.of R (MorseGenerators E f n s →₀ R) :=
  (rfl)

/-- The differential of the Morse complex with values in `s` from degree `n + 1` to degree `n` is
the Morse boundary with values in `s`. -/
theorem complexOn_d (n : ℕ) :
    (C.complexOn s).d (n + 1) n = ModuleCat.ofHom (C.boundaryOn s n) := by
  simp [complexOn]

/-- The differential of the Morse complex with values in `s` applied to a chain is its Morse
boundary with values in `s`. -/
@[simp]
theorem complexOn_d_apply (n : ℕ) (c : MorseGenerators E f (n + 1) s →₀ R) :
    (C.complexOn s).d (n + 1) n c = C.boundaryOn s n c := by
  rw [complexOn_d]
  -- The morphism `ModuleCat.ofHom g` applied to a chain is `g` applied to it, by definition.
  rfl

/-- The terms of the Morse complex with values in `s` are finitely generated. -/
instance finite_complexOn_X (n : ℕ) :
    Module.Finite R ((C.complexOn s).X n) := by
  have := C.finite_morseGenerators n s
  rw [complexOn_X]
  exact Module.Finite.finsupp

/-- The terms of the Morse complex with values in `s` are free. -/
instance free_complexOn_X (n : ℕ) : Module.Free R ((C.complexOn s).X n) := by
  rw [complexOn_X]
  exact Module.Free.finsupp _ _ _

/-- The term of the Morse complex with values in `s` in degree `n` has rank the number of
critical points of index `n` with value in `s`. -/
@[simp]
theorem finrank_complexOn_X [StrongRankCondition R] (n : ℕ) :
    finrank R ((C.complexOn s).X n) = Nat.card (MorseGenerators E f n s) := by
  have := C.finite_morseGenerators n s
  let _ := Fintype.ofFinite (MorseGenerators E f n s)
  -- The carrier of `ModuleCat.of R A` is `A` itself.
  exact (finrank_finsupp_self (R := R)).trans Nat.card_eq_fintype_card.symm

/-- If all critical values of critical points in `s` agree, all coefficients between these critical
points vanish, so the Morse boundary with values in `s` vanishes. -/
theorem boundaryOn_eq_zero {s : Set ℝ}
    (hs : ∀ p q : criticalPoints 𝓘(ℝ, E) f, f p ∈ s → f q ∈ s → f p = f q) (n : ℕ) :
    C.boundaryOn s n = 0 :=
  Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ by
    rw [boundaryOn_single_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply,
      C.coeff_eq_zero_of_value_le (hs p.val q.val p.property.2 q.property.2).le,
      mul_zero]

/-- **With a single critical value, the Morse complex has zero differential.** If all critical
values of critical points in `s` agree, every differential of the Morse complex with values in
`s` vanishes. -/
theorem complexOn_d_eq_zero
    (hs : ∀ p q : criticalPoints 𝓘(ℝ, E) f, f p ∈ s → f q ∈ s → f p = f q) (i j : ℕ) :
    (C.complexOn s).d i j = 0 := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · obtain rfl : j + 1 = i := hij
    rw [complexOn_d, C.boundaryOn_eq_zero hs, ModuleCat.ofHom_zero]
    -- Both sides are the zero morphism; they differ only in how the terms are written.
    rfl
  · exact (C.complexOn s).shape i j hij

/-! ### The Morse complex with all critical values -/

/-- **The Morse complex with all critical values on the critical points of each index.** Let
`d n` be linear maps from the free `R`-module on the critical points of index `n + 1` to that on
those of index `n`, squaring to zero, whose coefficient of `q` in the image of `p` is
`C.coeff p q`. Then the Morse complex with all critical values is the chain complex with these
differentials. -/
def complexOnUnivIso
    (d : ∀ n : ℕ,
      ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ R) →ₗ[R]
        ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R))
    (hd : ∀ n c q, d n c q = c.sum fun p a ↦ a * C.coeff p.val q.val)
    (hsq : ∀ n, d n ∘ₗ d (n + 1) = 0) :
    C.complexOn univ ≅ ChainComplex.of
      (fun n ↦ ModuleCat.of R
        ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R))
      (fun n ↦ ModuleCat.ofHom (d n))
      fun n ↦ by rw [← ModuleCat.ofHom_comp, hsq, ModuleCat.ofHom_zero] :=
  Hom.isoOfComponents
    (fun n ↦ (Finsupp.domLCongr (MorseGenerators.univEquiv E f n)).toModuleIso) <| by
    rintro _ n rfl
    rw [complexOn_d]
    -- `ChainComplex.of_d` writes the differential between the terms `ModuleCat.of R _`, so `rw`
    -- cannot rewrite it inside this composite, whose motive would not be type-correct; `simp only`
    -- can.
    simp only [ChainComplex.of_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun (c : MorseGenerators E f (n + 1) univ →₀ R) ↦
      Finsupp.ext fun q ↦ ?_)
    -- The terms of `complexOn` and of the target are `ModuleCat.of` of the chain modules only
    -- after unfolding these definitions, so the goal is not type-correct at reducible
    -- transparency and the `ModuleCat` composition lemmas do not rewrite it; `change` states it
    -- on the underlying chains instead.
    change d n (Finsupp.equivMapDomain _ c) q =
      Finsupp.equivMapDomain _ (C.boundaryOn univ n c) q
    rw [Finsupp.equivMapDomain_apply, boundaryOn_apply, hd, Finsupp.equivMapDomain_eq_mapDomain,
      Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul ..]
    simp

/-- The identification of the Morse complex with all critical values with the complex on the
critical points of each index sends a chain to the same chain. -/
@[simp]
theorem complexOnUnivIso_hom_f_apply
    (d : ∀ n : ℕ,
      ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ R) →ₗ[R]
        ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R))
    (hd : ∀ n c q, d n c q = c.sum fun p a ↦ a * C.coeff p.val q.val)
    (hsq : ∀ n, d n ∘ₗ d (n + 1) = 0) (n : ℕ) (c : MorseGenerators E f n univ →₀ R) :
    (C.complexOnUnivIso d hd hsq).hom.f n c = c.mapDomain (MorseGenerators.univEquiv E f n) :=
  -- The component is `(Finsupp.domLCongr _).toModuleIso`, whose application to a chain is
  -- `Finsupp.equivMapDomain` by definition of `Finsupp.domLCongr`.
  Finsupp.equivMapDomain_eq_mapDomain _ c

/-- The inverse identification of the complex on the critical points of each index with the Morse
complex with all critical values sends a chain to the same chain. -/
@[simp]
theorem complexOnUnivIso_inv_f_apply
    (d : ∀ n : ℕ,
      ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ R) →ₗ[R]
        ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R))
    (hd : ∀ n c q, d n c q = c.sum fun p a ↦ a * C.coeff p.val q.val)
    (hsq : ∀ n, d n ∘ₗ d (n + 1) = 0) (n : ℕ)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R) :
    (C.complexOnUnivIso d hd hsq).inv.f n c =
      c.mapDomain (MorseGenerators.univEquiv E f n).symm :=
  -- As above, the component applied to a chain is `Finsupp.equivMapDomain` by definition.
  Finsupp.equivMapDomain_eq_mapDomain _ c

/-! ### Inclusions and restrictions -/

variable {s t u}

/-- **The inclusion of a lower part.** If `s ⊆ t` and every value in `t` below a value of `s` lies
in `s`, the chains with values in `s` form a subcomplex of those with values in `t`: no nonzero
coefficient leaves `s` within `t`. -/
def complexOnInclusion (hst : s ⊆ t) (hlow : ∀ x ∈ t, ∀ y ∈ s, x < y → x ∈ s) :
    C.complexOn s ⟶ C.complexOn t where
  f n := ModuleCat.ofHom (Finsupp.lmapDomain R R (MorseGenerators.inclusion hst))
  comm' := by
    rintro _ n rfl
    rw [complexOn_d, complexOn_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun (c : MorseGenerators E f (n + 1) s →₀ R) ↦
      Finsupp.ext fun q ↦ ?_)
    -- The components are typed at the terms `(C.complexOn _).X n`, which are the modules
    -- `ModuleCat.of R (_ →₀ R)` only after unfolding `complexOn`, so the goal is
    -- not type-correct at reducible transparency and `ModuleCat.hom_comp`/`ModuleCat.hom_ofHom`
    -- do not rewrite it; `change` states it on the underlying chains instead.
    change C.boundaryOn t n (c.mapDomain (MorseGenerators.inclusion hst)) q =
      (C.boundaryOn s n c).mapDomain (MorseGenerators.inclusion hst) q
    rw [boundaryOn_apply,
      Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul ..]
    simp only [MorseGenerators.coe_inclusion]
    by_cases hq : f q.val ∈ s
    · obtain ⟨q', rfl⟩ := (MorseGenerators.mem_range_inclusion_iff hst q).2 hq
      rw [Finsupp.mapDomain_apply_of_injective (MorseGenerators.inclusion_injective hst),
        boundaryOn_apply]
      simp only [MorseGenerators.coe_inclusion]
    · -- No nonzero coefficient runs from `s` to a critical point of `t` outside `s`.
      rw [Finsupp.mapDomain_of_notMem_range _ _
        (mt (MorseGenerators.mem_range_inclusion_iff hst q).1 hq)]
      rw [Finsupp.sum]
      refine Finset.sum_eq_zero fun p _ ↦ ?_
      rw [C.coeff_eq_zero_of_value_le
        (not_lt.1 fun hlt ↦ hq (hlow _ q.property.2 _ p.property.2 hlt)), mul_zero]

/-- The inclusion of a lower part sends a chain to the same chain. -/
@[simp]
theorem complexOnInclusion_f_apply (hst : s ⊆ t) (hlow : ∀ x ∈ t, ∀ y ∈ s, x < y → x ∈ s)
    (n : ℕ) (c : MorseGenerators E f n s →₀ R) :
    (C.complexOnInclusion hst hlow).f n c = c.mapDomain (MorseGenerators.inclusion hst) :=
  (rfl)

/-- The inclusions of lower parts compose. -/
@[reassoc (attr := simp)]
theorem complexOnInclusion_comp_complexOnInclusion (hst : s ⊆ t) (htu : t ⊆ u)
    (hlow : ∀ x ∈ t, ∀ y ∈ s, x < y → x ∈ s) (hlow' : ∀ x ∈ u, ∀ y ∈ t, x < y → x ∈ t) :
    C.complexOnInclusion hst hlow ≫ C.complexOnInclusion htu hlow' =
      C.complexOnInclusion (hst.trans htu)
        (fun x hx y hy hxy ↦ hlow x (hlow' x hx y (hst hy) hxy) y hy hxy) := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (c : MorseGenerators E f n s →₀ R) ↦ ?_)
  -- The terms `(C.complexOn _).X n` are the modules `ModuleCat.of R (_ →₀ R)`
  -- only after unfolding `complexOn`, so `complexOnInclusion_f_apply` does not rewrite
  -- the composite applied to `c`; `change` states the goal on the underlying chains instead.
  change (c.mapDomain (MorseGenerators.inclusion hst)).mapDomain (MorseGenerators.inclusion htu) =
    c.mapDomain (MorseGenerators.inclusion (hst.trans htu))
  rw [← Finsupp.mapDomain_comp]
  exact congrArg (Finsupp.mapDomain · c) (funext (MorseGenerators.inclusion_inclusion hst htu))

/-- The inclusion of a lower part is injective in every degree. -/
instance mono_complexOnInclusion (hst : s ⊆ t) (hlow : ∀ x ∈ t, ∀ y ∈ s, x < y → x ∈ s) :
    Mono (C.complexOnInclusion hst hlow) :=
  mono_of_mono_f _ fun _ ↦ (ModuleCat.mono_iff_injective _).2 <|
    Finsupp.mapDomain_injective (MorseGenerators.inclusion_injective hst)

/-- **The restriction to an upper part.** If `s ⊆ t` and every value in `t` above a value of `s`
lies in `s`, restricting chains with values in `t` to the critical points with values in `s` is a
chain map: no nonzero coefficient enters `s` from outside within `t`. -/
def complexOnRestriction (hst : s ⊆ t) (hup : ∀ x ∈ t, ∀ y ∈ s, y < x → x ∈ s) :
    C.complexOn t ⟶ C.complexOn s where
  f n := ModuleCat.ofHom (Finsupp.lcomapDomain (MorseGenerators.inclusion hst)
    (MorseGenerators.inclusion_injective hst))
  comm' := by
    classical
    rintro _ n rfl
    have := C.finite_morseGenerators (n + 1) s
    have := C.finite_morseGenerators (n + 1) t
    let _ := Fintype.ofFinite (MorseGenerators E f (n + 1) s)
    let _ := Fintype.ofFinite (MorseGenerators E f (n + 1) t)
    rw [complexOn_d, complexOn_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun (c : MorseGenerators E f (n + 1) t →₀ R) ↦
      Finsupp.ext fun r ↦ ?_)
    -- The components are typed at the terms `(C.complexOn _).X n`, which are the modules
    -- `ModuleCat.of R (_ →₀ R)` only after unfolding `complexOn`, so the goal is
    -- not type-correct at reducible transparency and `ModuleCat.hom_comp`/`ModuleCat.hom_ofHom`
    -- do not rewrite it; `change` states it on the underlying chains instead.
    change C.boundaryOn s n (c.comapDomain (MorseGenerators.inclusion hst)
        (MorseGenerators.inclusion_injective hst).injOn) r =
      C.boundaryOn t n c (MorseGenerators.inclusion hst r)
    simp only [Finsupp.comapDomain_apply, boundaryOn_apply_eq_sum,
      MorseGenerators.coe_inclusion]
    refine Fintype.sum_of_injective (MorseGenerators.inclusion hst)
      (MorseGenerators.inclusion_injective hst) _ _ (fun p hp ↦ ?_) fun _ ↦ rfl
    -- No nonzero coefficient runs into `s` from a critical point of `t` outside `s`.
    rw [C.coeff_eq_zero_of_value_le (not_lt.1 fun hlt ↦
      hp ((MorseGenerators.mem_range_inclusion_iff hst p).2
        (hup _ p.property.2 _ r.property.2 hlt))), mul_zero]

/-- The restriction to an upper part keeps the coefficients of the critical points with values
in `s`. -/
@[simp]
theorem complexOnRestriction_f_apply (hst : s ⊆ t) (hup : ∀ x ∈ t, ∀ y ∈ s, y < x → x ∈ s)
    (n : ℕ) (c : MorseGenerators E f n t →₀ R) :
    (C.complexOnRestriction hst hup).f n c =
      c.comapDomain (MorseGenerators.inclusion hst)
        (MorseGenerators.inclusion_injective hst).injOn :=
  (rfl)

/-- The restriction to an upper part is surjective in every degree: a chain with values in `s` is
the restriction of its extension by zero. -/
instance epi_complexOnRestriction (hst : s ⊆ t) (hup : ∀ x ∈ t, ∀ y ∈ s, y < x → x ∈ s) :
    Epi (C.complexOnRestriction hst hup) :=
  epi_of_epi_f _ fun _ ↦ (ModuleCat.epi_iff_surjective _).2 fun c ↦
    ⟨c.mapDomain (MorseGenerators.inclusion hst),
      Finsupp.comapDomain_mapDomain _ (MorseGenerators.inclusion_injective hst) c⟩

/-! ### Sublevels and bands -/

/-- **The sublevel–band sequence.** For `a ≤ b`, the short complex of chain maps
`C(Iic a) → C(Iic b) → C(Ioc a b)` including the chains of the sublevel of `a` into those of the
sublevel of `b`, and restricting these to the band between them. -/
-- The body is exposed so that the terms and maps of the sequence compute to the sublevel and band
-- complexes and the inclusion and restriction between them, which the `@[simps]` lemmas state.
@[expose, simps]
def bandSequence {a b : ℝ} (hab : a ≤ b) :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk
    (C.complexOnInclusion (Iic_subset_Iic.2 hab) (fun _ _ _ hy hxy ↦ hxy.le.trans hy))
    (C.complexOnRestriction (s := Ioc a b) Ioc_subset_Iic_self
      (fun _ hx _ hy hyx ↦ ⟨hy.1.trans hyx, hx⟩)) <| by
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (c : MorseGenerators E f n (Iic a) →₀ R) ↦
      Finsupp.ext fun r ↦ ?_)
    -- The terms `(C.complexOn _).X n` are `ModuleCat.of` of the chain modules only after
    -- unfolding `complexOn`, so `complexOnInclusion_f_apply` and
    -- `complexOnRestriction_f_apply` do not rewrite the composite applied to `c`; `change`
    -- states the goal on the underlying chains instead.
    change (c.mapDomain (MorseGenerators.inclusion (Iic_subset_Iic.2 hab)))
      (MorseGenerators.inclusion Ioc_subset_Iic_self r) = 0
    rw [Finsupp.mapDomain_of_notMem_range _ _ fun hr ↦
      (not_le.2 r.property.2.1) ((MorseGenerators.mem_range_inclusion_iff _ _).1 hr)]

/-- **The sublevel–band sequence is short exact.** For `a ≤ b`, the chains of the sublevel of `a`
are the chains of the sublevel of `b` which vanish on the band `Ioc a b`. -/
theorem bandSequence_shortExact {a b : ℝ} (hab : a ≤ b) :
    (C.bandSequence hab).ShortExact := by
  refine shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  have hinj : Function.Injective (MorseGenerators.inclusion (E := E) (f := f) (n := n)
      (Iic_subset_Iic.2 hab)) := MorseGenerators.inclusion_injective _
  refine .mk' ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    fun (c : MorseGenerators E f n (Iic b) →₀ R) ↦ ⟨fun hc ↦ ?_, ?_⟩)
    ((ModuleCat.mono_iff_injective _).2 (Finsupp.mapDomain_injective hinj))
    (by
      -- Instance search sees neither the second map of the sequence as the restriction nor its
      -- image under `eval` as its component without unfolding these definitions, so the first
      -- is unfolded by `dsimp` and the second is stated with `inferInstanceAs`.
      have : Epi (C.bandSequence hab).g := by
        dsimp only [bandSequence]
        infer_instance
      exact inferInstanceAs (Epi ((C.bandSequence hab).g.f n)))
  · -- A chain vanishing on the band is the image of its restriction to the sublevel of `a`.
    refine ⟨c.comapDomain _ hinj.injOn, Finsupp.ext fun q ↦ ?_⟩
    -- As above, `complexOnInclusion_f_apply` does not rewrite the component applied to a
    -- chain, since the terms of `complexOn` are the chain modules only after unfolding it;
    -- `change` states the goal on the underlying chains instead.
    change (Finsupp.mapDomain _ _) q = c q
    by_cases hq : f q.val ≤ a
    · obtain ⟨q', rfl⟩ := (MorseGenerators.mem_range_inclusion_iff (Iic_subset_Iic.2 hab) q).2
        (show f q.val ∈ Iic a from hq)
      rw [Finsupp.mapDomain_apply_of_injective hinj, Finsupp.comapDomain_apply]
    · rw [Finsupp.mapDomain_of_notMem_range _ _
        (mt (MorseGenerators.mem_range_inclusion_iff _ q).1 hq)]
      -- `hc` states that the restriction of `c` to the band vanishes, with the restriction written
      -- as a component of the sublevel–band sequence applied to `c`.
      have hc' : c.comapDomain (MorseGenerators.inclusion (s := Ioc a b) Ioc_subset_Iic_self)
          (MorseGenerators.inclusion_injective _).injOn = 0 := hc
      exact (DFunLike.congr_fun hc' ⟨q.val, q.property.1, not_le.1 hq, q.property.2⟩).symm
  · rintro ⟨d, rfl⟩
    exact ShortComplex.moduleCat_zero_apply _ d


/-! ### The critical-value filtration and its spectral sequence -/

/-- The inclusion of the chains of the critical points with value at most `a` into the Morse
complex, both regraded as cochain complexes in nonpositive degrees along `n ↦ -n`. -/
def filtrationι (a : ℝ) :
    (C.complexOn (Iic a)).extend ComplexShape.embeddingDownNat ⟶
      (C.complexOn univ).extend ComplexShape.embeddingDownNat :=
  extendMap (C.complexOnInclusion (subset_univ _) fun _ _ _ hy hxy ↦ hxy.le.trans hy) _

/-- The inclusion of the regraded chains of the critical points with value at most `a` is the
regraded inclusion of the sublevel complex into the Morse complex. -/
theorem filtrationι_def (a : ℝ) :
    C.filtrationι a = extendMap (C.complexOnInclusion (subset_univ _)
      fun _ _ _ hy hxy ↦ hxy.le.trans hy) ComplexShape.embeddingDownNat :=
  (rfl)

instance mono_filtrationι (a : ℝ) : Mono (C.filtrationι a) := by
  rw [filtrationι]
  exact HomologicalComplex.mono_extendMap _ _

/-- **The critical-value filtration of the Morse complex.** For cut values `a : ℤ → ℝ`, the `q`th
stage is the subcomplex of the chains of the critical points with value at most `a q`, in the
Morse complex regraded as a cochain complex in nonpositive degrees along `n ↦ -n`. -/
def filtration (a : ℤ → ℝ) (q : ℤ) :
    Subobject ((C.complexOn univ).extend ComplexShape.embeddingDownNat) :=
  Subobject.mk (C.filtrationι (a q))

/-- The `q`th stage of the critical-value filtration is the subobject given by the regraded
sublevel chains of `a q`. -/
theorem filtration_eq_mk (a : ℤ → ℝ) (q : ℤ) :
    C.filtration a q = Subobject.mk (C.filtrationι (a q)) :=
  (rfl)

/-- For `a q ≤ a q'`, the inclusion of the sublevel chains of `a q` into the Morse complex factors
through those of `a q'`. -/
@[reassoc (attr := simp)]
theorem extendMap_complexOnInclusion_comp_filtrationι {a b : ℝ} (hab : a ≤ b) :
    extendMap (C.complexOnInclusion (Iic_subset_Iic.2 hab)
        (fun _ _ _ hy hxy ↦ hxy.le.trans hy)) ComplexShape.embeddingDownNat ≫
        C.filtrationι b =
      C.filtrationι a := by
  rw [filtrationι, filtrationι, ← extendMap_comp, complexOnInclusion_comp_complexOnInclusion]

variable {a : ℤ → ℝ}

/-- The critical-value filtration grows with the cut values. -/
theorem filtration_mono {q q' : ℤ} (hqq' : a q ≤ a q') :
    C.filtration a q ≤ C.filtration a q' :=
  Subobject.mk_le_mk_of_comm _ (C.extendMap_complexOnInclusion_comp_filtrationι hqq')

/-- For monotone cut values, the critical-value filtration is increasing. -/
theorem monotone_filtration (ha : Monotone a) : Monotone (C.filtration a) :=
  fun _ _ hqq' ↦ C.filtration_mono (ha hqq')

/-- Below all critical values, the critical-value filtration is zero. -/
theorem filtration_eq_bot {q : ℤ} (hq : ∀ p : criticalPoints 𝓘(ℝ, E) f, a q < f p) :
    C.filtration a q = ⊥ := by
  refine Subobject.mk_eq_bot_iff_zero.2 ?_
  have hzero : IsZero (C.complexOn (Iic (a q))) := by
    refine (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun n ↦ ?_)
    have : IsEmpty (MorseGenerators E f n (Iic (a q))) := ⟨fun p ↦ (hq p.val).not_ge p.property.2⟩
    have : Unique (MorseGenerators E f n (Iic (a q)) →₀ R) := Finsupp.uniqueOfLeft
    exact (ModuleCat.isZero_of_subsingleton
      (ModuleCat.of R (MorseGenerators E f n (Iic (a q)) →₀ R))).eq_of_src _ _
  exact ((ComplexShape.embeddingDownNat.extendFunctor _).map_isZero hzero).eq_of_src _ _

/-- Above all critical values, the critical-value filtration is everything. -/
theorem filtration_eq_top {q : ℤ} (hq : ∀ p : criticalPoints 𝓘(ℝ, E) f, f p ≤ a q) :
    C.filtration a q = ⊤ := by
  have : ∀ n, IsIso ((C.complexOnInclusion (subset_univ (Iic (a q)))
      (fun _ _ _ hy hxy ↦ hxy.le.trans hy)).f n) := fun n ↦
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨Finsupp.mapDomain_injective (MorseGenerators.inclusion_injective _),
        Finsupp.mapDomain_surjective fun p ↦ ⟨⟨p.val, p.property.1, hq p.val⟩, rfl⟩⟩
  have := Hom.isIso_of_components (C.complexOnInclusion (subset_univ (Iic (a q)))
    (fun _ _ _ hy hxy ↦ hxy.le.trans hy))
  have : IsIso (C.filtrationι (a q)) := by
    rw [filtrationι]
    exact Functor.map_isIso (ComplexShape.embeddingDownNat.extendFunctor _) _
  exact Subobject.mk_eq_top_of_isIso _

variable (ha : Monotone a)

/-- **The graded pieces of the critical-value filtration are the band complexes.** The quotient of
the stage `a (q + 1)` of the filtration by the stage `a q`, as the cokernel of a transition map of
the functor `CochainComplex.filtrationFunctor` of the filtration, is the regraded complex of the
chains of the critical points with value in `Ioc (a q) (a (q + 1))`. The isomorphism is induced by
restricting chains to the band
(`TauCeti.MorseBoundaryCoeffs.π_filtrationCokernelIso_hom`). -/
def filtrationCokernelIso (q : ℤ) :
    cokernel ((CochainComplex.filtrationFunctor _ (C.monotone_filtration ha)).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q = q) rfl))) ≅
      (C.complexOn (Ioc (a q) (a (q + 1)))).extend ComplexShape.embeddingDownNat :=
  CochainComplex.cokernelFiltrationFunctorMapIsoOfIsColimit _ _
    (fun q ↦ C.filtrationι (a q)) (C.filtration_eq_mk a) q _
    (C.extendMap_complexOnInclusion_comp_filtrationι (ha (Int.le_add_one le_rfl))) _ _
    ((C.bandSequence_shortExact (ha (Int.le_add_one le_rfl))).extend
      ComplexShape.embeddingDownNat).gIsCokernel

/-- The identification of the graded piece of the critical-value filtration with the band complex
restricts chains to the band: under the identification of the stage `a (q + 1)` with the sublevel
chains, the cokernel projection is the restriction to the band `Ioc (a q) (a (q + 1))`. -/
@[reassoc (attr := simp)]
theorem π_filtrationCokernelIso_hom (q : ℤ) :
    cokernel.π _ ≫ (C.filtrationCokernelIso ha q).hom =
      (CochainComplex.filtrationFunctorObjIsoOfEqMk _ (C.monotone_filtration ha)
          (C.filtrationι (a (q + 1))) (C.filtration_eq_mk a (q + 1))).hom ≫
        extendMap (C.complexOnRestriction (s := Ioc (a q) (a (q + 1))) Ioc_subset_Iic_self
          (fun _ hx _ hy hyx ↦ ⟨hy.1.trans hyx, hx⟩)) ComplexShape.embeddingDownNat :=
  CochainComplex.π_cokernelFiltrationFunctorMapIsoOfIsColimit_hom _ _ _ _ _ _ _ _ _ _

/-- **The critical-value spectral sequence of the Morse complex.** For monotone cut values
`a : ℤ → ℝ`, the spectral sequence of the filtration of the Morse complex by the chains of
the critical points with value at most `a q`, in the cohomological indexing of
`CochainComplex.spectralSequence`: chains in degree `n` sit in degree `-n`. -/
abbrev spectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor _ (C.monotone_filtration ha))

/-- **The first page of the critical-value spectral sequence.** The object at `(p, q)` on the
first page (numbered `2`, as in `CochainComplex.spectralSequence`) is the homology in degree `n`
of the Morse complex of the band `Ioc (a q) (a (q + 1))`, where `p + q = -n`. -/
def spectralSequenceFirstPageXIso (pq : ℤ × ℤ) (n : ℕ) (hn : pq.1 + pq.2 = -n) :
    ((C.spectralSequence ha).page 2).X pq ≅
      (C.complexOn (Ioc (a pq.2) (a (pq.2 + 1)))).homology n :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
    (homologyFunctor _ _ _).mapIso (C.filtrationCokernelIso ha pq.2) ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat hn.symm

/-- **The first page of the critical-value spectral sequence for a single critical value per
band.** If all critical values in the band `Ioc (a q) (a (q + 1))` agree, the object at `(p, q)`
on the first page, with `p + q = -n`, is the free `R`-module on the critical points of index
`n` in the band. -/
def spectralSequenceFirstPageXIsoOfSubsingleton (pq : ℤ × ℤ) (n : ℕ)
    (hn : pq.1 + pq.2 = -n)
    (hband : ∀ p q : criticalPoints 𝓘(ℝ, E) f, f p ∈ Ioc (a pq.2) (a (pq.2 + 1)) →
      f q ∈ Ioc (a pq.2) (a (pq.2 + 1)) → f p = f q) :
    ((C.spectralSequence ha).page 2).X pq ≅
      ModuleCat.of R (MorseGenerators E f n (Ioc (a pq.2) (a (pq.2 + 1))) →₀ R) :=
  C.spectralSequenceFirstPageXIso ha pq n hn ≪≫
    ((C.complexOn _).XIsoHomologyOfDEqZero n
      (C.complexOn_d_eq_zero _ hband _ _)
      (C.complexOn_d_eq_zero _ hband _ _)).symm

/-- If all critical values in the band `Ioc (a q) (a (q + 1))` agree, the object at `(p, q)` on the
first page of the critical-value spectral sequence, with `p + q = -n`, has rank the number of
critical points of index `n` in the band. -/
theorem finrank_spectralSequence_page_two_X [StrongRankCondition R] (pq : ℤ × ℤ) (n : ℕ)
    (hn : pq.1 + pq.2 = -n)
    (hband : ∀ p q : criticalPoints 𝓘(ℝ, E) f, f p ∈ Ioc (a pq.2) (a (pq.2 + 1)) →
      f q ∈ Ioc (a pq.2) (a (pq.2 + 1)) → f p = f q) :
    finrank R (((C.spectralSequence ha).page 2).X pq) =
      Nat.card (MorseGenerators E f n (Ioc (a pq.2) (a (pq.2 + 1)))) :=
  (C.spectralSequenceFirstPageXIsoOfSubsingleton ha pq n hn
    hband).toLinearEquiv.finrank_eq.trans (C.finrank_complexOn_X _ n)

/-- **The abutment of the critical-value spectral sequence** in degree `-n` is the Morse homology
in degree `n`, the homology of the Morse complex with all critical values. -/
def filtrationAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (C.monotone_filtration ha))).abutment (-n) ≅
      (C.complexOn univ).homology n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat rfl

/-- The abutment of the critical-value spectral sequence in degree `-n` is the homology in degree
`n` of any complex isomorphic to the Morse complex with all critical values. -/
def filtrationAbutmentIsoOfIso {K : ChainComplex (ModuleCat R) ℕ} (e : C.complexOn univ ≅ K)
    (n : ℕ) :
    (CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (C.monotone_filtration ha))).abutment (-n) ≅
      K.homology n :=
  C.filtrationAbutmentIso ha n ≪≫ (homologyFunctor _ _ n).mapIso e

/-- **Strong convergence of the critical-value spectral sequence.** If `a q₀` lies below and
`a q₁` above all critical values, then on every page `r ≥ 2` with `q - r + 2 ≤ q₀` and
`q₁ ≤ q + r - 1`, the object at `(p, q)` is the graded piece `F_{q+1} H / F_q H` of the
filtration of the abutment in degree `p + q`, which is the Morse homology in degree `-(p + q)` by
`TauCeti.MorseBoundaryCoeffs.filtrationAbutmentIso`. -/
def spectralSequencePageXIsoGraded {q₀ q₁ : ℤ}
    (h₀ : ∀ p : criticalPoints 𝓘(ℝ, E) f, a q₀ < f p)
    (h₁ : ∀ p : criticalPoints 𝓘(ℝ, E) f, f p ≤ a q₁) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (hr₀ : pq.2 - r + 2 ≤ q₀) (hr₁ : q₁ ≤ pq.2 + r - 1) :
    ((C.spectralSequence ha).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (C.monotone_filtration ha))).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite _ _
    (C.filtration_eq_bot h₀) (C.filtration_eq_top h₁) r hr pq hr₀ hr₁

end MorseBoundaryCoeffs

end TauCeti
