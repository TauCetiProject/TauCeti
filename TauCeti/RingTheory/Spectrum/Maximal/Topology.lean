/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Maximal.Topology
public import Mathlib.Topology.NoetherianSpace

import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.Connected.Clopen

/-!
# Topology of maximal spectra

`MaximalSpectrum R` carries the subspace topology induced from `PrimeSpectrum R` along
`MaximalSpectrum.toPrimeSpectrum`. This file develops its principal Zariski open basis
`MaximalSpectrum.basicOpen`, Noetherianity over Noetherian rings, and the relation between
idempotents and clopen subsets over commutative and Jacobson rings.

## Main definitions

* `MaximalSpectrum.basicOpen`: the principal Zariski open `{x | f ∉ x.asIdeal}` of
  `MaximalSpectrum R`.

## Main results

* `MaximalSpectrum.isEmbedding_toPrimeSpectrum`: the inclusion into `PrimeSpectrum R` is a
  topological embedding.
* `MaximalSpectrum.isTopologicalBasis_basic_opens`: principal Zariski opens form a basis of the
  Zariski topology on `MaximalSpectrum R`.
* `MaximalSpectrum.instNoetherianSpace`: the maximal spectrum of a Noetherian ring is Noetherian.
* `MaximalSpectrum.basicOpen_injOn_isIdempotentElem`: `basicOpen` is injective on idempotents.
* `MaximalSpectrum.isClopen_iff`: over a Jacobson ring, clopen subsets of `MaximalSpectrum R` are
  precisely the principal opens of idempotents.
* `MaximalSpectrum.connectedSpace_iff_idempotent`: the maximal spectrum of a nontrivial Jacobson
  ring is connected if and only if its only idempotents are `0` and `1`.
-/

public section

namespace MaximalSpectrum

open TopologicalSpace Topology

variable {R : Type*} [CommRing R]

/-- The natural inclusion of the maximal spectrum into the prime spectrum is a topological
embedding. -/
theorem isEmbedding_toPrimeSpectrum : IsEmbedding (@toPrimeSpectrum R _) :=
  ⟨⟨rfl⟩, toPrimeSpectrum_injective⟩

/-- The principal Zariski open subset `{x ∈ MaximalSpectrum R | r ∉ x.asIdeal}`. -/
def basicOpen (r : R) : Opens (MaximalSpectrum R) :=
  (PrimeSpectrum.basicOpen r).comap ⟨toPrimeSpectrum, toPrimeSpectrum_continuous⟩

@[simp]
theorem mem_basicOpen (f : R) (x : MaximalSpectrum R) : x ∈ basicOpen f ↔ f ∉ x.asIdeal := Iff.rfl

theorem coe_basicOpen (f : R) :
    (basicOpen f : Set (MaximalSpectrum R)) = {x | f ∉ x.asIdeal} := (rfl)

theorem preimage_toPrimeSpectrum_basicOpen (f : R) :
    toPrimeSpectrum ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) = basicOpen f := (rfl)

@[simp]
theorem basicOpen_one : basicOpen (1 : R) = ⊤ := by ext; simp [Ideal.IsPrime.one_notMem]

@[simp]
theorem basicOpen_zero : basicOpen (0 : R) = ⊥ := by ext; simp

theorem basicOpen_mul (f g : R) : basicOpen (f * g) = basicOpen f ⊓ basicOpen g := by
  ext; simp [Ideal.IsPrime.mul_mem_iff_mem_or_mem]

theorem basicOpen_pow (f : R) (n : ℕ) (hn : 0 < n) : basicOpen (f ^ n) = basicOpen f := by
  ext x; exact congrArg (toPrimeSpectrum x ∈ ·) (PrimeSpectrum.basicOpen_pow f n hn) |>.to_iff

/-- A principal Zariski open is `⊤` if and only if its defining element is a unit. -/
theorem basicOpen_eq_top_iff (f : R) : basicOpen f = ⊤ ↔ IsUnit f := by
  rw [Opens.ext_iff, Opens.coe_top, Set.eq_univ_iff_forall]
  refine ⟨fun h ↦ ?_, fun hf x hx ↦ x.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hf)⟩
  by_contra hf
  obtain ⟨m, hm, hfm⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hf)
  exact h ⟨m, hm⟩ (hfm (Ideal.subset_span (Set.mem_singleton f)))

/-- For every `f : R`, `basicOpen f` and `basicOpen (1 - f)` cover `MaximalSpectrum R`. -/
theorem basicOpen_sup_basicOpen_one_sub (f : R) : basicOpen f ⊔ basicOpen (1 - f) = ⊤ := by
  ext x; refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
  rw [SetLike.mem_coe, Opens.mem_sup, mem_basicOpen, mem_basicOpen]
  by_contra! h
  exact x.isMaximal.ne_top
    (Ideal.eq_top_of_isUnit_mem _ (add_sub_cancel f 1 ▸ x.asIdeal.add_mem h.1 h.2) isUnit_one)

/-- Principal Zariski opens form a basis of the open sets of `MaximalSpectrum R`. -/
theorem isBasis_basic_opens : Opens.IsBasis (Set.range (@basicOpen R _)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp U.isOpen
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff.mp
    (hV.mem_nhds (Set.mem_preimage.mp (hVU.symm ▸ SetLike.mem_coe.mpr hx)))
  exact ⟨basicOpen f, ⟨f, rfl⟩, hxf, SetLike.coe_subset_coe.mp (hVU ▸ Set.preimage_mono hfV)⟩

/-- Principal Zariski opens form a topological basis of `MaximalSpectrum R`. -/
theorem isTopologicalBasis_basic_opens :
    IsTopologicalBasis (Set.range fun r : R ↦ (basicOpen r : Set (MaximalSpectrum R))) := by
  simpa only [Opens.IsBasis, ← Set.range_comp, Function.comp_def] using isBasis_basic_opens (R := R)

/-- The maximal spectrum of a Noetherian ring is a Noetherian topological space. -/
instance instNoetherianSpace [IsNoetherianRing R] : NoetherianSpace (MaximalSpectrum R) :=
  isEmbedding_toPrimeSpectrum.isInducing.noetherianSpace

section Idempotent

variable {e : R}

/-- The principal Zariski open of an idempotent is clopen in `MaximalSpectrum R`. -/
theorem isClopen_basicOpen_of_isIdempotentElem (he : IsIdempotentElem e) :
    IsClopen (basicOpen e : Set (MaximalSpectrum R)) :=
  (PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩).preimage toPrimeSpectrum_continuous

/-- For an idempotent `e`, `basicOpen e` and `basicOpen (1 - e)` are disjoint. -/
theorem disjoint_basicOpen_one_sub (he : IsIdempotentElem e) :
    Disjoint (basicOpen e) (basicOpen (1 - e)) := by
  rw [disjoint_iff, ← basicOpen_mul, mul_sub, mul_one, he.eq, sub_self, basicOpen_zero]

/-- For an idempotent `e`, `basicOpen e` is empty if and only if `e = 0`. -/
theorem basicOpen_eq_bot_iff_of_isIdempotentElem (he : IsIdempotentElem e) :
    basicOpen e = ⊥ ↔ e = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ basicOpen_zero⟩
  have htop : basicOpen (1 - e) = ⊤ := by simpa [h] using basicOpen_sup_basicOpen_one_sub e
  exact (((basicOpen_eq_top_iff (1 - e)).mp htop).mul_right_eq_zero).mp
    (by rw [sub_mul, one_mul, he.eq, sub_self])

/-- For an idempotent `e`, `basicOpen e` is `⊤` if and only if `e = 1`. -/
theorem basicOpen_eq_top_iff_of_isIdempotentElem (he : IsIdempotentElem e) :
    basicOpen e = ⊤ ↔ e = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ basicOpen_one⟩
  have hbot : basicOpen (1 - e) = ⊥ := eq_bot_iff.mpr
    (disjoint_iff.mp (disjoint_basicOpen_one_sub he).symm ▸ le_inf le_rfl (h ▸ le_top))
  exact (sub_eq_zero.mp ((basicOpen_eq_bot_iff_of_isIdempotentElem he.one_sub).mp hbot)).symm

/-- Principal Zariski opens distinguish idempotents over any commutative ring. -/
theorem basicOpen_injOn_isIdempotentElem :
    Set.InjOn (@basicOpen R _) {e : R | IsIdempotentElem e} := by
  intro e₁ he₁ e₂ he₂ h
  have hd {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
      (hab : basicOpen a = basicOpen b) : a = a * b :=
    sub_eq_zero.mp <| by
      simpa [mul_sub] using (basicOpen_eq_bot_iff_of_isIdempotentElem (ha.mul hb.one_sub)).mp
        (by rw [basicOpen_mul, hab, disjoint_iff.mp (disjoint_basicOpen_one_sub hb)])
  exact (hd he₁ he₂ h).trans (mul_comm e₁ e₂ ▸ (hd he₂ he₁ h.symm).symm)

end Idempotent

section Jacobson

/-- Over a Jacobson ring, the clopen subsets of `MaximalSpectrum R` are precisely the principal
opens of idempotent elements. -/
theorem isClopen_iff [IsJacobsonRing R] {s : Set (MaximalSpectrum R)} :
    IsClopen s ↔ ∃ e : R, IsIdempotentElem e ∧ s = basicOpen e := by
  refine ⟨fun hs ↦ ?_, fun ⟨e, he, hs⟩ ↦ hs ▸ isClopen_basicOpen_of_isIdempotentElem he⟩
  obtain ⟨Z₁, hZ₁, hZ₁s⟩ := isClosed_induced_iff.mp hs.isClosed
  obtain ⟨Z₂, hZ₂, hZ₂s⟩ := isClosed_induced_iff.mp hs.compl.isClosed
  have hrange : Set.range (@toPrimeSpectrum R _) = closedPoints (PrimeSpectrum R) :=
    toPrimeSpectrum_range
  have hdisj : Z₁ ∩ Z₂ = ∅ := by
    by_contra! hne
    obtain ⟨x, hxZ, hxcl⟩ := nonempty_inter_closedPoints hne (hZ₁.inter hZ₂).isLocallyClosed
    obtain ⟨m, rfl⟩ := hrange ▸ hxcl
    exact (hZ₂s ▸ hxZ.2 : m ∈ sᶜ) (hZ₁s ▸ hxZ.1)
  have hcov : Z₁ ∪ Z₂ = Set.univ := by
    rw [← Set.compl_empty_iff]; by_contra! hne
    obtain ⟨x, hxU, hxcl⟩ :=
      nonempty_inter_closedPoints hne (hZ₁.union hZ₂).isOpen_compl.isLocallyClosed
    obtain ⟨m, rfl⟩ := hrange ▸ hxcl
    exact (em (m ∈ s)).elim (fun hm ↦ hxU (.inl (Set.mem_preimage.mp (hZ₁s.symm ▸ hm))))
      fun hm ↦ hxU (.inr (Set.mem_preimage.mp (hZ₂s.symm ▸ hm)))
  have hcompl : Z₁ᶜ = Z₂ := Set.ext fun x ↦ ⟨fun hx ↦ (hcov ▸ Set.mem_univ x).resolve_left hx,
    fun hx₂ hx₁ ↦ Set.notMem_empty x (hdisj ▸ ⟨hx₁, hx₂⟩)⟩
  obtain ⟨e, he, rfl⟩ :=
    PrimeSpectrum.isClopen_iff.mp ⟨hZ₁, isClosed_compl_iff.mp (hcompl.symm ▸ hZ₂)⟩
  exact ⟨e, he, hZ₁s.symm⟩

/-- The maximal spectrum of a nontrivial Jacobson ring is connected if and only if the only
idempotents of the ring are `0` and `1`. -/
theorem connectedSpace_iff_idempotent [Nontrivial R] [IsJacobsonRing R] :
    ConnectedSpace (MaximalSpectrum R) ↔ ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [connectedSpace_iff_clopen]
  refine ⟨fun ⟨_, h⟩ e he ↦ ?_, fun h ↦ ⟨inferInstance, fun s hs ↦ ?_⟩⟩
  · exact (h _ (isClopen_basicOpen_of_isIdempotentElem he)).imp
      (fun hb ↦ (basicOpen_eq_bot_iff_of_isIdempotentElem he).mp (Opens.ext hb))
      (fun ht ↦ (basicOpen_eq_top_iff_of_isIdempotentElem he).mp (Opens.ext ht))
  · obtain ⟨e, he, rfl⟩ := isClopen_iff.mp hs
    rcases h e he with rfl | rfl <;> simp

end Jacobson

end MaximalSpectrum
