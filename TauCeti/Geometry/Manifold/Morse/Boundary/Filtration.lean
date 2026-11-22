/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.ChainComplex
public import TauCeti.Algebra.Homology.Embedding.Extend.Homology.Sequence
public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
import TauCeti.Algebra.Homology.Embedding.Extend.Subobject

/-!
# The critical-value filtration of the mod-two Morse complex

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a Morse–Smale
pseudo-gradient adapted to `f`. Every trajectory strictly lowers the value of `f`, so the mod-two
Morse boundary of a critical point `p` only involves critical points of smaller critical value
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.value_lt_of_morseBoundaryCoeff_ne_zero`). This file
uses this to filter the mod-two Morse complex by critical values and studies the spectral sequence
of the filtration.

* **Morse chains with values in a set.** For an order-connected set `s` of real numbers, the
  critical points with critical value in `s` span a complex
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplexOn`): its term in degree `n` is the
  free `ZMod 2`-module on the critical points of index `n` with value in `s`
  (`TauCeti.MorseGenerators`), and its differential counts the trajectories between them. The
  differential squares to zero because a broken trajectory from `p` to `r` through `q` has
  `f r < f q < f p`, so `q` has its value in `s` whenever `p` and `r` do. For `s = univ` this is
  the mod-two Morse complex (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplexOnUnivIso`).
* **Sublevels and bands.** For `a ≤ b`, the chains of the sublevel `Iic a` form a subcomplex of
  those of `Iic b`, and the quotient is the complex of the band `Ioc a b`: the sequence
  `0 → C(Iic a) → C(Iic b) → C(Ioc a b) → 0` is a short exact sequence of complexes
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplexBandSequence_shortExact`). When all
  critical values in the band agree, the band complex has zero differential, so its homology in
  degree `n` is the free module on the critical points of index `n` in the band.
* **The critical-value spectral sequence.** For a monotone sequence `a : ℤ → ℝ` of cut values, the
  sublevel complexes of the `a q` form an increasing filtration of the Morse complex
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseFiltration`), regraded as a cochain complex
  in nonpositive degrees along `n ↦ -n`. Its spectral sequence
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseSpectralSequence`) has on its first page
  (numbered `2` in the indexing of `CochainComplex.spectralSequence`), at `(p, q)` with
  `p + q = -n`, the homology in degree `n` of the band `Ioc (a q) (a (q + 1))`
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseSpectralSequenceFirstPageXIso`). If each band
  contains at most one critical value, this is the free `ZMod 2`-module on the critical points of
  index `n` in the band
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseSpectralSequenceFirstPageXIsoOfSubsingleton`).
  If some `a q` lies below and some `a q'` above all critical values, the filtration is finite and
  the spectral sequence converges strongly to the Morse homology: on every late enough page the
  object at `(p, q)` is the graded piece of the induced filtration of the Morse homology in degree
  `-(p + q)` (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseSpectralSequencePageXIsoGraded`,
  with abutment `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseFiltrationAbutmentIso`).

The singular counterpart, the spectral sequence of the filtration of `M` by the sublevels
`{f ≤ a q}`, is `TauCeti.Geometry.Manifold.Morse.SpectralSequence`. For a critical-band cut its
first page is also free on the critical points in each band; comparing the two spectral sequences
through a filtered chain map is not attempted here. The regrading of the filtration and the
identification of its graded pieces and abutment follow the singular construction
`TauCeti.chainFiltration` in `TauCeti.AlgebraicTopology.Singular.FilteredSpace.ChainFunctor`.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `morseComplexOn`: the mod-two Morse complex of the critical points with value in `s`.
* `morseComplexOnInclusion`, `morseComplexOnRestriction`: the chain maps between these complexes
  for a lower and for an upper part of `s`.
* `morseComplexOnUnivIso`: for `s = univ` it is the mod-two Morse complex.
* `morseComplexOn_d_eq_zero`: with at most one critical value in `s`, the differential vanishes.
* `morseComplexBandSequence_shortExact`: the short exact sequence of a sublevel, a larger sublevel
  and the band between them.
* `morseFiltration`: the critical-value filtration of the regraded Morse complex.
* `morseSpectralSequence`: its spectral sequence.
* `morseSpectralSequenceFirstPageXIso`, `morseSpectralSequenceFirstPageXIsoOfSubsingleton`,
  `finrank_morseSpectralSequence_page_two_X`: its first page.
* `morseFiltrationAbutmentIso`, `morseSpectralSequencePageXIsoGraded`: its convergence to Morse
  homology.

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
in degree `n` of the mod-two Morse chains with critical values in `s`. -/
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

end MorseGenerators

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- A Morse function on a compact manifold has finitely many critical points of each index with
value in a given set. -/
theorem IsMorse.finite_morseGenerators (hf : IsMorse 𝓘(ℝ, E) f) (n : ℕ) (s : Set ℝ) :
    Finite (MorseGenerators E f n s) :=
  haveI := hf.finite_criticalPoints.to_subtype
  inferInstance

variable [FiniteDimensional ℝ E] [T2Space M] {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

/-! ### Morse chains with critical values in a set -/

/-- **The Morse boundary with critical values in `s`.** The `ZMod 2`-linear map from the free
module on the critical points of index `n + 1` with value in `s` to the free module on those of
index `n`, sending `p` to the sum of the critical points `q`, each weighted by the number of
trajectories from `p` to `q` modulo two. -/
def morseBoundaryOn (s : Set ℝ) (n : ℕ) :
    (MorseGenerators E f (n + 1) s →₀ ZMod 2) →ₗ[ZMod 2] (MorseGenerators E f n s →₀ ZMod 2) :=
  haveI := hf.finite_morseGenerators n s
  Finsupp.linearCombination (ZMod 2) fun p ↦
    Finsupp.ofSupportFinite (fun q ↦ h.morseBoundaryCoeff hf p.val q.val) (toFinite _)

/-- The coefficient of `q` in the Morse boundary with values in `s` of a chain `c` is the sum over
the critical points `p` of `c p` times the number of trajectories from `p` to `q` modulo two. -/
theorem morseBoundaryOn_apply {s : Set ℝ} {n : ℕ} (c : MorseGenerators E f (n + 1) s →₀ ZMod 2)
    (q : MorseGenerators E f n s) :
    h.morseBoundaryOn hf s n c q = c.sum fun p a ↦ a * h.morseBoundaryCoeff hf p.val q.val := by
  simp [morseBoundaryOn, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

/-- The coefficient of `q` in the Morse boundary with values in `s` of `a • p` is `a` times the
number of trajectories from `p` to `q` modulo two. -/
@[simp]
theorem morseBoundaryOn_single_apply {s : Set ℝ} {n : ℕ} (p : MorseGenerators E f (n + 1) s)
    (a : ZMod 2) (q : MorseGenerators E f n s) :
    h.morseBoundaryOn hf s n (Finsupp.single p a) q = a * h.morseBoundaryCoeff hf p.val q.val := by
  rw [morseBoundaryOn_apply, Finsupp.sum_single_index (zero_mul _)]

/-- The Morse boundary with values in `s` as a sum over all critical points of index `n + 1` with
value in `s`. -/
private theorem morseBoundaryOn_apply_eq_sum {s : Set ℝ} {n : ℕ}
    [Fintype (MorseGenerators E f (n + 1) s)] (c : MorseGenerators E f (n + 1) s →₀ ZMod 2)
    (q : MorseGenerators E f n s) :
    h.morseBoundaryOn hf s n c q = ∑ p, c p * h.morseBoundaryCoeff hf p.val q.val := by
  rw [morseBoundaryOn_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]

/-- **The Morse boundary with values in an order-connected set squares to zero.** A broken
trajectory from `p` to `r` through `q` has `f r < f q < f p`, so if the values of `p` and `r` lie
in the order-connected set `s`, so does that of `q`. -/
@[simp]
theorem morseBoundaryOn_comp_morseBoundaryOn (s : Set ℝ) [s.OrdConnected] (n : ℕ) :
    h.morseBoundaryOn hf s n ∘ₗ h.morseBoundaryOn hf s (n + 1) = 0 := by
  classical
  have := hf.finite_criticalPoints.to_subtype
  let _ := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  let _ := Fintype.ofFinite (MorseGenerators E f (n + 1) s)
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
  rw [LinearMap.comp_apply, morseBoundaryOn_apply_eq_sum, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  simp only [morseBoundaryOn_single_apply, mul_assoc, ← Finset.mul_sum]
  refine mul_eq_zero_of_right _ ?_
  rw [← h.sum_morseBoundaryCoeff_mul_morseBoundaryCoeff hf p.val r.val]
  refine Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
    (fun q hq ↦ ?_) fun _ ↦ rfl
  -- A critical point outside the generators contributes nothing.
  by_contra hne
  have h₁ : h.morseBoundaryCoeff hf p.val q ≠ 0 := left_ne_zero_of_mul hne
  have h₂ : h.morseBoundaryCoeff hf q r.val ≠ 0 := right_ne_zero_of_mul hne
  refine hq ⟨⟨q, ?_, Set.OrdConnected.out ‹_› r.property.2 p.property.2
    ⟨(h.value_lt_of_morseBoundaryCoeff_ne_zero hf h₂).le,
      (h.value_lt_of_morseBoundaryCoeff_ne_zero hf h₁).le⟩⟩, rfl⟩
  have := h.morseIndex_eq_add_one_of_morseBoundaryCoeff_ne_zero hf h₁
  have := p.property.1
  omega

/-- **The mod-two Morse complex with critical values in `s`.** For an order-connected set `s`, the
chain complex of `ZMod 2`-vector spaces whose term in degree `n` is the free module on the
critical points of index `n` with critical value in `s`, with the differential counting
trajectories modulo two. For `s = univ` it is the mod-two Morse complex
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplexOnUnivIso`). -/
-- The body is exposed so that the terms of the complex compute to the free modules on the
-- critical points, which the statements of `morseComplexOn_X` and `morseComplexOn_d` need.
@[expose]
def morseComplexOn (s : Set ℝ) [s.OrdConnected] : ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of (ZMod 2) (MorseGenerators E f n s →₀ ZMod 2))
    (fun n ↦ ModuleCat.ofHom (h.morseBoundaryOn hf s n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, h.morseBoundaryOn_comp_morseBoundaryOn hf, ModuleCat.ofHom_zero]

variable (s t u : Set ℝ) [s.OrdConnected] [t.OrdConnected] [u.OrdConnected]

/-- The term of the Morse complex with values in `s` in degree `n` is the free `ZMod 2`-module on
the critical points of index `n` with value in `s`. -/
@[simp]
theorem morseComplexOn_X (n : ℕ) :
    (h.morseComplexOn hf s).X n = ModuleCat.of (ZMod 2) (MorseGenerators E f n s →₀ ZMod 2) :=
  (rfl)

/-- The differential of the Morse complex with values in `s` from degree `n + 1` to degree `n` is
the Morse boundary with values in `s`. -/
theorem morseComplexOn_d (n : ℕ) :
    (h.morseComplexOn hf s).d (n + 1) n = ModuleCat.ofHom (h.morseBoundaryOn hf s n) := by
  simp [morseComplexOn]

/-- The differential of the Morse complex with values in `s` applied to a chain is its Morse
boundary with values in `s`. -/
@[simp]
theorem morseComplexOn_d_apply (n : ℕ) (c : MorseGenerators E f (n + 1) s →₀ ZMod 2) :
    (h.morseComplexOn hf s).d (n + 1) n c = h.morseBoundaryOn hf s n c := by
  rw [morseComplexOn_d]
  -- The morphism `ModuleCat.ofHom g` applied to a chain is `g` applied to it, by definition.
  rfl

/-- The terms of the Morse complex with values in `s` are finite-dimensional. -/
instance finite_morseComplexOn_X (n : ℕ) :
    Module.Finite (ZMod 2) ((h.morseComplexOn hf s).X n) := by
  have := hf.finite_morseGenerators n s
  rw [morseComplexOn_X]
  exact Module.Finite.finsupp

/-- The term of the Morse complex with values in `s` in degree `n` has dimension the number of
critical points of index `n` with value in `s`. -/
@[simp]
theorem finrank_morseComplexOn_X (n : ℕ) :
    finrank (ZMod 2) ((h.morseComplexOn hf s).X n) = Nat.card (MorseGenerators E f n s) := by
  have := hf.finite_morseGenerators n s
  let _ := Fintype.ofFinite (MorseGenerators E f n s)
  -- The carrier of `ModuleCat.of (ZMod 2) A` is `A` itself.
  exact (finrank_finsupp_self (R := ZMod 2)).trans Nat.card_eq_fintype_card.symm

/-- If all critical values of critical points in `s` agree, there are no trajectories between
these critical points, so the Morse boundary with values in `s` vanishes. -/
theorem morseBoundaryOn_eq_zero {s : Set ℝ}
    (hs : ∀ p q : criticalPoints 𝓘(ℝ, E) f, f p ∈ s → f q ∈ s → f p = f q) (n : ℕ) :
    h.morseBoundaryOn hf s n = 0 :=
  Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ by
    rw [morseBoundaryOn_single_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply,
      h.morseBoundaryCoeff_eq_zero_of_value_le hf (hs p.val q.val p.property.2 q.property.2).le,
      mul_zero]

/-- **With a single critical value, the Morse complex has zero differential.** If all critical
values of critical points in `s` agree, every differential of the Morse complex with values in
`s` vanishes. -/
theorem morseComplexOn_d_eq_zero
    (hs : ∀ p q : criticalPoints 𝓘(ℝ, E) f, f p ∈ s → f q ∈ s → f p = f q) (i j : ℕ) :
    (h.morseComplexOn hf s).d i j = 0 := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · obtain rfl : j + 1 = i := hij
    rw [morseComplexOn_d, h.morseBoundaryOn_eq_zero hf hs, ModuleCat.ofHom_zero]
    -- Both sides are the zero morphism; they differ only in how the terms are written.
    rfl
  · exact (h.morseComplexOn hf s).shape i j hij

/-! ### Inclusions and restrictions -/

variable {s t u}

/-- **The inclusion of a lower part.** If `s ⊆ t` and every value in `t` below a value of `s` lies
in `s`, the chains with values in `s` form a subcomplex of those with values in `t`: no trajectory
leaves `s` within `t`. -/
def morseComplexOnInclusion (hst : s ⊆ t) (hlow : ∀ x ∈ t, ∀ y ∈ s, x < y → x ∈ s) :
    h.morseComplexOn hf s ⟶ h.morseComplexOn hf t where
  f n := ModuleCat.ofHom (Finsupp.lmapDomain (ZMod 2) (ZMod 2) (MorseGenerators.inclusion hst))
  comm' := by
    rintro _ n rfl
    rw [morseComplexOn_d, morseComplexOn_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun (c : MorseGenerators E f (n + 1) s →₀ ZMod 2) ↦
      Finsupp.ext fun q ↦ ?_)
    -- The components are typed at the terms `(h.morseComplexOn hf _).X n`, which are the modules
    -- `ModuleCat.of (ZMod 2) (_ →₀ ZMod 2)` only after unfolding `morseComplexOn`, so the goal is
    -- not type-correct at reducible transparency and `ModuleCat.hom_comp`/`ModuleCat.hom_ofHom`
    -- do not rewrite it; `change` states it on the underlying chains instead.
    change h.morseBoundaryOn hf t n (c.mapDomain (MorseGenerators.inclusion hst)) q =
      (h.morseBoundaryOn hf s n c).mapDomain (MorseGenerators.inclusion hst) q
    rw [morseBoundaryOn_apply,
      Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul ..]
    simp only [MorseGenerators.coe_inclusion]
    by_cases hq : f q.val ∈ s
    · obtain ⟨q', rfl⟩ := (MorseGenerators.mem_range_inclusion_iff hst q).2 hq
      rw [Finsupp.mapDomain_apply_of_injective (MorseGenerators.inclusion_injective hst),
        morseBoundaryOn_apply]
      simp only [MorseGenerators.coe_inclusion]
    · -- No trajectory runs from `s` to a critical point of `t` outside `s`.
      rw [Finsupp.mapDomain_of_notMem_range _ _
        (mt (MorseGenerators.mem_range_inclusion_iff hst q).1 hq)]
      rw [Finsupp.sum]
      refine Finset.sum_eq_zero fun p _ ↦ ?_
      rw [h.morseBoundaryCoeff_eq_zero_of_value_le hf
        (not_lt.1 fun hlt ↦ hq (hlow _ q.property.2 _ p.property.2 hlt)), mul_zero]

/-- The inclusion of a lower part sends a chain to the same chain. -/
@[simp]
theorem morseComplexOnInclusion_f_apply (hst : s ⊆ t) (hlow : ∀ x ∈ t, ∀ y ∈ s, x < y → x ∈ s)
    (n : ℕ) (c : MorseGenerators E f n s →₀ ZMod 2) :
    (h.morseComplexOnInclusion hf hst hlow).f n c = c.mapDomain (MorseGenerators.inclusion hst) :=
  (rfl)

/-- The inclusions of lower parts compose. -/
@[reassoc (attr := simp)]
theorem morseComplexOnInclusion_comp_morseComplexOnInclusion (hst : s ⊆ t) (htu : t ⊆ u)
    (hlow : ∀ x ∈ t, ∀ y ∈ s, x < y → x ∈ s) (hlow' : ∀ x ∈ u, ∀ y ∈ t, x < y → x ∈ t) :
    h.morseComplexOnInclusion hf hst hlow ≫ h.morseComplexOnInclusion hf htu hlow' =
      h.morseComplexOnInclusion hf (hst.trans htu)
        (fun x hx y hy hxy ↦ hlow x (hlow' x hx y (hst hy) hxy) y hy hxy) := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (c : MorseGenerators E f n s →₀ ZMod 2) ↦ ?_)
  -- The terms `(h.morseComplexOn hf _).X n` are the modules `ModuleCat.of (ZMod 2) (_ →₀ ZMod 2)`
  -- only after unfolding `morseComplexOn`, so `morseComplexOnInclusion_f_apply` does not rewrite
  -- the composite applied to `c`; `change` states the goal on the underlying chains instead.
  change (c.mapDomain (MorseGenerators.inclusion hst)).mapDomain (MorseGenerators.inclusion htu) =
    c.mapDomain (MorseGenerators.inclusion (hst.trans htu))
  rw [← Finsupp.mapDomain_comp]
  exact congrArg (Finsupp.mapDomain · c) (funext (MorseGenerators.inclusion_inclusion hst htu))

/-- The inclusion of a lower part is injective in every degree. -/
instance mono_morseComplexOnInclusion (hst : s ⊆ t) (hlow : ∀ x ∈ t, ∀ y ∈ s, x < y → x ∈ s) :
    Mono (h.morseComplexOnInclusion hf hst hlow) :=
  mono_of_mono_f _ fun _ ↦ (ModuleCat.mono_iff_injective _).2 <|
    Finsupp.mapDomain_injective (MorseGenerators.inclusion_injective hst)

/-- **The restriction to an upper part.** If `s ⊆ t` and every value in `t` above a value of `s`
lies in `s`, restricting chains with values in `t` to the critical points with values in `s` is a
chain map: no trajectory enters `s` from outside within `t`. -/
def morseComplexOnRestriction (hst : s ⊆ t) (hup : ∀ x ∈ t, ∀ y ∈ s, y < x → x ∈ s) :
    h.morseComplexOn hf t ⟶ h.morseComplexOn hf s where
  f n := ModuleCat.ofHom (Finsupp.lcomapDomain (MorseGenerators.inclusion hst)
    (MorseGenerators.inclusion_injective hst))
  comm' := by
    classical
    rintro _ n rfl
    have := hf.finite_morseGenerators (n + 1) s
    have := hf.finite_morseGenerators (n + 1) t
    let _ := Fintype.ofFinite (MorseGenerators E f (n + 1) s)
    let _ := Fintype.ofFinite (MorseGenerators E f (n + 1) t)
    rw [morseComplexOn_d, morseComplexOn_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun (c : MorseGenerators E f (n + 1) t →₀ ZMod 2) ↦
      Finsupp.ext fun r ↦ ?_)
    -- The components are typed at the terms `(h.morseComplexOn hf _).X n`, which are the modules
    -- `ModuleCat.of (ZMod 2) (_ →₀ ZMod 2)` only after unfolding `morseComplexOn`, so the goal is
    -- not type-correct at reducible transparency and `ModuleCat.hom_comp`/`ModuleCat.hom_ofHom`
    -- do not rewrite it; `change` states it on the underlying chains instead.
    change h.morseBoundaryOn hf s n (c.comapDomain (MorseGenerators.inclusion hst)
        (MorseGenerators.inclusion_injective hst).injOn) r =
      h.morseBoundaryOn hf t n c (MorseGenerators.inclusion hst r)
    simp only [Finsupp.comapDomain_apply, morseBoundaryOn_apply_eq_sum,
      MorseGenerators.coe_inclusion]
    refine Fintype.sum_of_injective (MorseGenerators.inclusion hst)
      (MorseGenerators.inclusion_injective hst) _ _ (fun p hp ↦ ?_) fun _ ↦ rfl
    -- No trajectory runs into `s` from a critical point of `t` outside `s`.
    rw [h.morseBoundaryCoeff_eq_zero_of_value_le hf (not_lt.1 fun hlt ↦
      hp ((MorseGenerators.mem_range_inclusion_iff hst p).2
        (hup _ p.property.2 _ r.property.2 hlt))), mul_zero]

/-- The restriction to an upper part keeps the coefficients of the critical points with values
in `s`. -/
@[simp]
theorem morseComplexOnRestriction_f_apply (hst : s ⊆ t) (hup : ∀ x ∈ t, ∀ y ∈ s, y < x → x ∈ s)
    (n : ℕ) (c : MorseGenerators E f n t →₀ ZMod 2) :
    (h.morseComplexOnRestriction hf hst hup).f n c =
      c.comapDomain (MorseGenerators.inclusion hst)
        (MorseGenerators.inclusion_injective hst).injOn :=
  (rfl)

/-- The restriction to an upper part is surjective in every degree: a chain with values in `s` is
the restriction of its extension by zero. -/
instance epi_morseComplexOnRestriction (hst : s ⊆ t) (hup : ∀ x ∈ t, ∀ y ∈ s, y < x → x ∈ s) :
    Epi (h.morseComplexOnRestriction hf hst hup) :=
  epi_of_epi_f _ fun _ ↦ (ModuleCat.epi_iff_surjective _).2 fun c ↦
    ⟨c.mapDomain (MorseGenerators.inclusion hst),
      Finsupp.comapDomain_mapDomain _ (MorseGenerators.inclusion_injective hst) c⟩

/-! ### The Morse complex itself -/

/-- The critical points of index `n` with value anywhere are the critical points of index `n`. -/
private def morseGeneratorsUnivEquiv (n : ℕ) :
    MorseGenerators E f n univ ≃
      {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} :=
  Equiv.subtypeEquivRight fun _ ↦ and_iff_left (mem_univ _)

/-- **The Morse complex with all critical values is the Morse complex.** -/
def morseComplexOnUnivIso : h.morseComplexOn hf univ ≅ h.morseComplex hf :=
  Hom.isoOfComponents (fun n ↦ (Finsupp.domLCongr (morseGeneratorsUnivEquiv n)).toModuleIso) <| by
    rintro _ n rfl
    rw [morseComplexOn_d, morseComplex_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun (c : MorseGenerators E f (n + 1) univ →₀ ZMod 2) ↦
      Finsupp.ext fun q ↦ ?_)
    -- The terms of `morseComplexOn` and `morseComplex` are `ModuleCat.of` of the chain modules
    -- only after unfolding these definitions, so the goal is not type-correct at reducible
    -- transparency and the `ModuleCat` composition lemmas do not rewrite it; `change` states it
    -- on the underlying chains instead.
    change h.morseBoundaryAt hf n (Finsupp.equivMapDomain _ c) q =
      Finsupp.equivMapDomain _ (h.morseBoundaryOn hf univ n c) q
    rw [Finsupp.equivMapDomain_apply, morseBoundaryOn_apply, morseBoundaryAt_apply,
      Finsupp.equivMapDomain_eq_mapDomain,
      Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul ..]
    simp only [morseGeneratorsUnivEquiv, Equiv.subtypeEquivRight_apply_coe,
      Equiv.subtypeEquivRight_symm_apply_coe]

/-- The identification of the Morse complex with all critical values with the Morse complex sends
a chain to the same chain. -/
@[simp]
theorem morseComplexOnUnivIso_hom_f_apply (n : ℕ) (c : MorseGenerators E f n univ →₀ ZMod 2) :
    (h.morseComplexOnUnivIso hf).hom.f n c = c.mapDomain fun p ↦ ⟨p.val, p.property.1⟩ :=
  -- The component is `(Finsupp.domLCongr _).toModuleIso`, whose application to a chain is
  -- `Finsupp.equivMapDomain` by definition of `Finsupp.domLCongr`.
  Finsupp.equivMapDomain_eq_mapDomain _ c

/-- The inverse identification of the Morse complex with the Morse complex with all critical values
sends a chain to the same chain. -/
@[simp]
theorem morseComplexOnUnivIso_inv_f_apply (n : ℕ)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ ZMod 2) :
    (h.morseComplexOnUnivIso hf).inv.f n c = c.mapDomain fun p ↦ ⟨p.val, p.property, mem_univ _⟩ :=
  -- As above, the component applied to a chain is `Finsupp.equivMapDomain` by definition.
  Finsupp.equivMapDomain_eq_mapDomain _ c

/-! ### Sublevels and bands -/

/-- **The sublevel subcomplex.** The inclusion of the Morse chains of the critical points with
value at most `a` into the mod-two Morse complex. -/
def morseSublevelι (a : ℝ) : h.morseComplexOn hf (Iic a) ⟶ h.morseComplex hf :=
  h.morseComplexOnInclusion hf (subset_univ _) (fun _ _ _ hy hxy ↦ hxy.le.trans hy) ≫
    (h.morseComplexOnUnivIso hf).hom

/-- The sublevel subcomplex inclusion sends a chain to the same chain. -/
@[simp]
theorem morseSublevelι_f_apply (a : ℝ) (n : ℕ) (c : MorseGenerators E f n (Iic a) →₀ ZMod 2) :
    (h.morseSublevelι hf a).f n c = c.mapDomain fun p ↦ ⟨p.val, p.property.1⟩ := by
  simp only [morseSublevelι, comp_f, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_def,
    morseComplexOnInclusion_f_apply, morseComplexOnUnivIso_hom_f_apply, ← Finsupp.mapDomain_comp,
    Function.comp_apply, MorseGenerators.coe_inclusion]
  -- The two maps of generators differ only in the proofs of the index condition.
  rfl

instance mono_morseSublevelι (a : ℝ) : Mono (h.morseSublevelι hf a) := by
  rw [morseSublevelι]
  infer_instance

/-- For `a ≤ b`, the inclusion of the sublevel chains of `a` into the Morse complex factors
through the sublevel chains of `b`. -/
@[reassoc (attr := simp)]
theorem morseComplexOnInclusion_comp_morseSublevelι {a b : ℝ} (hab : a ≤ b) :
    h.morseComplexOnInclusion hf (Iic_subset_Iic.2 hab) (fun _ _ _ hy hxy ↦ hxy.le.trans hy) ≫
        h.morseSublevelι hf b =
      h.morseSublevelι hf a := by
  rw [morseSublevelι, morseSublevelι, morseComplexOnInclusion_comp_morseComplexOnInclusion_assoc]

/-- **The sublevel–band sequence.** For `a ≤ b`, the short complex of chain maps
`C(Iic a) → C(Iic b) → C(Ioc a b)` including the chains of the sublevel of `a` into those of the
sublevel of `b`, and restricting these to the band between them. -/
-- The body is exposed so that the terms and maps of the sequence compute to the sublevel and band
-- complexes and the inclusion and restriction between them, which the `@[simps]` lemmas state.
@[expose, simps]
def morseComplexBandSequence {a b : ℝ} (hab : a ≤ b) :
    ShortComplex (ChainComplex (ModuleCat (ZMod 2)) ℕ) :=
  ShortComplex.mk
    (h.morseComplexOnInclusion hf (Iic_subset_Iic.2 hab) (fun _ _ _ hy hxy ↦ hxy.le.trans hy))
    (h.morseComplexOnRestriction hf (s := Ioc a b) Ioc_subset_Iic_self
      (fun _ hx _ hy hyx ↦ ⟨hy.1.trans hyx, hx⟩)) <| by
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (c : MorseGenerators E f n (Iic a) →₀ ZMod 2) ↦
      Finsupp.ext fun r ↦ ?_)
    -- The terms `(h.morseComplexOn hf _).X n` are `ModuleCat.of` of the chain modules only after
    -- unfolding `morseComplexOn`, so `morseComplexOnInclusion_f_apply` and
    -- `morseComplexOnRestriction_f_apply` do not rewrite the composite applied to `c`; `change`
    -- states the goal on the underlying chains instead.
    change (c.mapDomain (MorseGenerators.inclusion (Iic_subset_Iic.2 hab)))
      (MorseGenerators.inclusion Ioc_subset_Iic_self r) = 0
    rw [Finsupp.mapDomain_of_notMem_range _ _ fun hr ↦
      (not_le.2 r.property.2.1) ((MorseGenerators.mem_range_inclusion_iff _ _).1 hr)]

/-- **The sublevel–band sequence is short exact.** For `a ≤ b`, the chains of the sublevel of `a`
are the chains of the sublevel of `b` which vanish on the band `Ioc a b`. -/
theorem morseComplexBandSequence_shortExact {a b : ℝ} (hab : a ≤ b) :
    (h.morseComplexBandSequence hf hab).ShortExact := by
  refine shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  have hinj : Function.Injective (MorseGenerators.inclusion (E := E) (f := f) (n := n)
      (Iic_subset_Iic.2 hab)) := MorseGenerators.inclusion_injective _
  refine .mk' ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    fun (c : MorseGenerators E f n (Iic b) →₀ ZMod 2) ↦ ⟨fun hc ↦ ?_, ?_⟩)
    ((ModuleCat.mono_iff_injective _).2 (Finsupp.mapDomain_injective hinj))
    (by
      -- Instance search sees neither the second map of the sequence as the restriction nor its
      -- image under `eval` as its component without unfolding these definitions, so the first
      -- is unfolded by `dsimp` and the second is stated with `inferInstanceAs`.
      have : Epi (h.morseComplexBandSequence hf hab).g := by
        dsimp only [morseComplexBandSequence]
        infer_instance
      exact inferInstanceAs (Epi ((h.morseComplexBandSequence hf hab).g.f n)))
  · -- A chain vanishing on the band is the image of its restriction to the sublevel of `a`.
    refine ⟨c.comapDomain _ hinj.injOn, Finsupp.ext fun q ↦ ?_⟩
    -- As above, `morseComplexOnInclusion_f_apply` does not rewrite the component applied to a
    -- chain, since the terms of `morseComplexOn` are the chain modules only after unfolding it;
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

/-- The inclusion of the chains of the critical points with value at most `a` into the mod-two
Morse complex, both regraded as cochain complexes in nonpositive degrees along `n ↦ -n`. -/
def morseFiltrationι (a : ℝ) :
    (h.morseComplexOn hf (Iic a)).extend ComplexShape.embeddingDownNat ⟶
      (h.morseComplex hf).extend ComplexShape.embeddingDownNat :=
  extendMap (h.morseSublevelι hf a) _

instance mono_morseFiltrationι (a : ℝ) : Mono (h.morseFiltrationι hf a) := by
  rw [morseFiltrationι]
  exact HomologicalComplex.mono_extendMap _ _

/-- **The critical-value filtration of the Morse complex.** For cut values `a : ℤ → ℝ`, the `q`th
stage is the subcomplex of the chains of the critical points with value at most `a q`, in the
mod-two Morse complex regraded as a cochain complex in nonpositive degrees along `n ↦ -n`. -/
def morseFiltration (a : ℤ → ℝ) (q : ℤ) :
    Subobject ((h.morseComplex hf).extend ComplexShape.embeddingDownNat) :=
  Subobject.mk (h.morseFiltrationι hf (a q))

/-- The `q`th stage of the critical-value filtration is the subobject given by the regraded
sublevel chains of `a q`. -/
theorem morseFiltration_eq_mk (a : ℤ → ℝ) (q : ℤ) :
    h.morseFiltration hf a q = Subobject.mk (h.morseFiltrationι hf (a q)) :=
  (rfl)

/-- For `a q ≤ a q'`, the inclusion of the sublevel chains of `a q` into the Morse complex factors
through those of `a q'`. -/
@[reassoc (attr := simp)]
theorem extendMap_morseComplexOnInclusion_comp_morseFiltrationι {a b : ℝ} (hab : a ≤ b) :
    extendMap (h.morseComplexOnInclusion hf (Iic_subset_Iic.2 hab)
        (fun _ _ _ hy hxy ↦ hxy.le.trans hy)) ComplexShape.embeddingDownNat ≫
        h.morseFiltrationι hf b =
      h.morseFiltrationι hf a := by
  rw [morseFiltrationι, morseFiltrationι, ← extendMap_comp,
    h.morseComplexOnInclusion_comp_morseSublevelι hf hab]

variable {a : ℤ → ℝ}

/-- The critical-value filtration grows with the cut values. -/
theorem morseFiltration_mono {q q' : ℤ} (hqq' : a q ≤ a q') :
    h.morseFiltration hf a q ≤ h.morseFiltration hf a q' :=
  Subobject.mk_le_mk_of_comm _ (h.extendMap_morseComplexOnInclusion_comp_morseFiltrationι hf hqq')

/-- For monotone cut values, the critical-value filtration is increasing. -/
theorem monotone_morseFiltration (ha : Monotone a) : Monotone (h.morseFiltration hf a) :=
  fun _ _ hqq' ↦ h.morseFiltration_mono hf (ha hqq')

/-- Below all critical values, the critical-value filtration is zero. -/
theorem morseFiltration_eq_bot {q : ℤ} (hq : ∀ p : criticalPoints 𝓘(ℝ, E) f, a q < f p) :
    h.morseFiltration hf a q = ⊥ := by
  refine Subobject.mk_eq_bot_iff_zero.2 ?_
  have hzero : IsZero (h.morseComplexOn hf (Iic (a q))) := by
    refine (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun n ↦ ?_)
    have : IsEmpty (MorseGenerators E f n (Iic (a q))) := ⟨fun p ↦ (hq p.val).not_ge p.property.2⟩
    have : Unique (MorseGenerators E f n (Iic (a q)) →₀ ZMod 2) := Finsupp.uniqueOfLeft
    exact (ModuleCat.isZero_of_subsingleton
      (ModuleCat.of (ZMod 2) (MorseGenerators E f n (Iic (a q)) →₀ ZMod 2))).eq_of_src _ _
  exact ((ComplexShape.embeddingDownNat.extendFunctor _).map_isZero hzero).eq_of_src _ _

/-- Above all critical values, the critical-value filtration is everything. -/
theorem morseFiltration_eq_top {q : ℤ} (hq : ∀ p : criticalPoints 𝓘(ℝ, E) f, f p ≤ a q) :
    h.morseFiltration hf a q = ⊤ := by
  have : ∀ n, IsIso ((h.morseComplexOnInclusion hf (subset_univ (Iic (a q)))
      (fun _ _ _ hy hxy ↦ hxy.le.trans hy)).f n) := fun n ↦
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨Finsupp.mapDomain_injective (MorseGenerators.inclusion_injective _),
        Finsupp.mapDomain_surjective fun p ↦ ⟨⟨p.val, p.property.1, hq p.val⟩, rfl⟩⟩
  have : IsIso (h.morseSublevelι hf (a q)) := by
    rw [morseSublevelι]
    have := Hom.isIso_of_components (h.morseComplexOnInclusion hf (subset_univ (Iic (a q)))
      (fun _ _ _ hy hxy ↦ hxy.le.trans hy))
    infer_instance
  have : IsIso (h.morseFiltrationι hf (a q)) := by
    rw [morseFiltrationι]
    exact Functor.map_isIso (ComplexShape.embeddingDownNat.extendFunctor _) _
  exact Subobject.mk_eq_top_of_isIso _

variable (ha : Monotone a)

/-- **The graded pieces of the critical-value filtration are the band complexes.** The quotient of
the stage `a (q + 1)` of the filtration by the stage `a q`, as the cokernel of a transition map of
the functor `CochainComplex.filtrationFunctor` of the filtration, is the regraded complex of the
chains of the critical points with value in `Ioc (a q) (a (q + 1))`. The isomorphism is induced by
restricting chains to the band
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.π_morseFiltrationCokernelIso_hom`). -/
def morseFiltrationCokernelIso (q : ℤ) :
    cokernel ((CochainComplex.filtrationFunctor _ (h.monotone_morseFiltration hf ha)).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q = q) rfl))) ≅
      (h.morseComplexOn hf (Ioc (a q) (a (q + 1)))).extend ComplexShape.embeddingDownNat :=
  CochainComplex.cokernelFiltrationFunctorMapIsoOfIsColimit _ _
    (fun q ↦ h.morseFiltrationι hf (a q)) (h.morseFiltration_eq_mk hf a) q _
    (h.extendMap_morseComplexOnInclusion_comp_morseFiltrationι hf (ha (Int.le_add_one le_rfl))) _ _
    ((h.morseComplexBandSequence_shortExact hf (ha (Int.le_add_one le_rfl))).extend
      ComplexShape.embeddingDownNat).gIsCokernel

/-- The identification of the graded piece of the critical-value filtration with the band complex
restricts chains to the band: under the identification of the stage `a (q + 1)` with the sublevel
chains, the cokernel projection is the restriction to the band `Ioc (a q) (a (q + 1))`. -/
@[reassoc (attr := simp)]
theorem π_morseFiltrationCokernelIso_hom (q : ℤ) :
    cokernel.π _ ≫ (h.morseFiltrationCokernelIso hf ha q).hom =
      (CochainComplex.filtrationFunctorObjIsoOfEqMk _ (h.monotone_morseFiltration hf ha)
          (fun q ↦ h.morseFiltrationι hf (a q)) (h.morseFiltration_eq_mk hf a) (q + 1)).hom ≫
        extendMap (h.morseComplexOnRestriction hf (s := Ioc (a q) (a (q + 1))) Ioc_subset_Iic_self
          (fun _ hx _ hy hyx ↦ ⟨hy.1.trans hyx, hx⟩)) ComplexShape.embeddingDownNat :=
  CochainComplex.π_cokernelFiltrationFunctorMapIsoOfIsColimit_hom _ _ _ _ _ _ _ _ _ _

/-- **The critical-value spectral sequence of the mod-two Morse complex.** For monotone cut values
`a : ℤ → ℝ`, the spectral sequence of the filtration of the mod-two Morse complex by the chains of
the critical points with value at most `a q`, in the cohomological indexing of
`CochainComplex.spectralSequence`: chains in degree `n` sit in degree `-n`. -/
abbrev morseSpectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor _ (h.monotone_morseFiltration hf ha))

/-- **The first page of the critical-value spectral sequence.** The object at `(p, q)` on the
first page (numbered `2`, as in `CochainComplex.spectralSequence`) is the homology in degree `n`
of the Morse complex of the band `Ioc (a q) (a (q + 1))`, where `p + q = -n`. -/
def morseSpectralSequenceFirstPageXIso (pq : ℤ × ℤ) (n : ℕ) (hn : pq.1 + pq.2 = -n) :
    ((h.morseSpectralSequence hf ha).page 2).X pq ≅
      (h.morseComplexOn hf (Ioc (a pq.2) (a (pq.2 + 1)))).homology n :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
    (homologyFunctor _ _ _).mapIso (h.morseFiltrationCokernelIso hf ha pq.2) ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat hn.symm

/-- **The first page of the critical-value spectral sequence for a single critical value per
band.** If all critical values in the band `Ioc (a q) (a (q + 1))` agree, the object at `(p, q)`
on the first page, with `p + q = -n`, is the free `ZMod 2`-module on the critical points of index
`n` in the band. -/
def morseSpectralSequenceFirstPageXIsoOfSubsingleton (pq : ℤ × ℤ) (n : ℕ)
    (hn : pq.1 + pq.2 = -n)
    (hband : ∀ p q : criticalPoints 𝓘(ℝ, E) f, f p ∈ Ioc (a pq.2) (a (pq.2 + 1)) →
      f q ∈ Ioc (a pq.2) (a (pq.2 + 1)) → f p = f q) :
    ((h.morseSpectralSequence hf ha).page 2).X pq ≅
      ModuleCat.of (ZMod 2) (MorseGenerators E f n (Ioc (a pq.2) (a (pq.2 + 1))) →₀ ZMod 2) :=
  h.morseSpectralSequenceFirstPageXIso hf ha pq n hn ≪≫
    ((h.morseComplexOn hf _).XIsoHomologyOfDEqZero n
      (h.morseComplexOn_d_eq_zero hf _ hband _ _)
      (h.morseComplexOn_d_eq_zero hf _ hband _ _)).symm

/-- If all critical values in the band `Ioc (a q) (a (q + 1))` agree, the object at `(p, q)` on the
first page of the critical-value spectral sequence, with `p + q = -n`, has dimension the number of
critical points of index `n` in the band. -/
theorem finrank_morseSpectralSequence_page_two_X (pq : ℤ × ℤ) (n : ℕ) (hn : pq.1 + pq.2 = -n)
    (hband : ∀ p q : criticalPoints 𝓘(ℝ, E) f, f p ∈ Ioc (a pq.2) (a (pq.2 + 1)) →
      f q ∈ Ioc (a pq.2) (a (pq.2 + 1)) → f p = f q) :
    finrank (ZMod 2) (((h.morseSpectralSequence hf ha).page 2).X pq) =
      Nat.card (MorseGenerators E f n (Ioc (a pq.2) (a (pq.2 + 1)))) :=
  (h.morseSpectralSequenceFirstPageXIsoOfSubsingleton hf ha pq n hn
    hband).toLinearEquiv.finrank_eq.trans (h.finrank_morseComplexOn_X hf _ n)

/-- **The abutment of the critical-value spectral sequence** in degree `-n` is the mod-two Morse
homology in degree `n`. -/
def morseFiltrationAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (h.monotone_morseFiltration hf ha))).abutment (-n) ≅
      (h.morseComplex hf).homology n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat rfl

/-- **Strong convergence of the critical-value spectral sequence.** If `a q₀` lies below and
`a q₁` above all critical values, then on every page `r ≥ 2` with `q - r + 2 ≤ q₀` and
`q₁ ≤ q + r - 1`, the object at `(p, q)` is the graded piece `F_{q+1} H / F_q H` of the
filtration of the abutment in degree `p + q`, which is the Morse homology in degree `-(p + q)` by
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseFiltrationAbutmentIso`. -/
def morseSpectralSequencePageXIsoGraded {q₀ q₁ : ℤ}
    (h₀ : ∀ p : criticalPoints 𝓘(ℝ, E) f, a q₀ < f p)
    (h₁ : ∀ p : criticalPoints 𝓘(ℝ, E) f, f p ≤ a q₁) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (hr₀ : pq.2 - r + 2 ≤ q₀) (hr₁ : q₁ ≤ pq.2 + r - 1) :
    ((h.morseSpectralSequence hf ha).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (h.monotone_morseFiltration hf ha))).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite _ _
    (h.morseFiltration_eq_bot hf h₀) (h.morseFiltration_eq_top hf h₁) r hr pq hr₀ hr₁

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
