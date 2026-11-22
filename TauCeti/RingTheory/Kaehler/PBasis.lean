/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.PBasis
public import TauCeti.RingTheory.Kaehler.DualDerivation
public import TauCeti.RingTheory.Kaehler.Frobenius

/-!
# `p`-bases and Kähler differentials

Let `k` be a field of prime characteristic `p` and `R` a commutative ring with an algebra map into
`k` whose image lies in the Frobenius subfield `k ^ p = (frobenius k p).fieldRange` (for instance,
`R = ℤ`, `R = ZMod p`, `R = k ^ p`, or any perfect ring `R` of characteristic `p`).

Every `R`-derivation out of `k` vanishes on `k ^ p`, so `Ω[k⁄R]` is canonically isomorphic to
`Ω[k⁄k ^ p]`. From a `p`-basis `b : ι → k`, the coordinate `k ^ p`-derivations
`hb.coordDerivation j` lift to dual forms on `Ω[k⁄R]`, showing that `D R k ∘ b` is a `k`-basis of
`Ω[k⁄R]`, and evaluation on `b` identifies `Derivation R k M` with `ι → M`. Combining this with
the existence of possibly infinite `p`-bases yields the equivalences between `p`-independence and
`k`-linear independence of differentials, between `p`-bases and `k`-bases of `Ω[k⁄R]`, the kernel
identification `ker (D R k) = k ^ p`, the finiteness criterion
`FiniteDimensional k Ω[k⁄R] ↔ FiniteDimensional (frobenius k p).fieldRange k`, and the degree
formula `[k : k ^ p] = p ^ dim_k Ω[k⁄R]` when `[k : k ^ p]` is finite.

## Main definitions

* `TauCeti.IsPBasis.kaehlerBasis`: the `k`-basis `i ↦ D R k (b i)` of `Ω[k⁄R]` associated to a
  `p`-basis `b`.
* `TauCeti.IsPBasis.derivationEquiv`: evaluation on `b` as a `k`-linear equivalence
  `Derivation R k M ≃ₗ[k] (ι → M)`.

## Main results

* `TauCeti.IsPBasis.coordDerivation_eq_dualDerivation`: `hb.coordDerivation j` is the derivation
  dual to `hb.kaehlerBasis` over `k ^ p`.
* `TauCeti.isPIndependent_of_linearIndependent_D`,
  `TauCeti.isPIndependent_iff_linearIndependent_D`: a family is `p`-independent iff its
  differentials are linearly independent over `k`.
* `TauCeti.isPBasis_iff_linearIndependent_and_span_D`: a family is a `p`-basis iff its
  differentials form a `k`-basis of `Ω[k⁄R]`.
* `TauCeti.D_eq_zero_iff_mem_fieldRange_frobenius`: `D R k x = 0 ↔ x ∈ (frobenius k p).fieldRange`.
* `TauCeti.finiteDimensional_kaehlerDifferential_iff`: `Ω[k⁄R]` is finite-dimensional over `k` iff
  `k` is finite-dimensional over `k ^ p`.
* `TauCeti.finrank_fieldRange_frobenius_eq_pow_finrank_kaehlerDifferential`:
  `[k : k ^ p] = p ^ Module.finrank k Ω[k⁄R]` when `[k : k ^ p]` is finite.
* `TauCeti.subsingleton_kaehlerDifferential_iff_perfectRing`: `Ω[k⁄R]` vanishes iff `k` is perfect.

## References

* D. Clausen, A. Mathew, M. Morrow, *K-theory and topological cyclic homology of henselian pairs*,
  J. Amer. Math. Soc. 34 (2021), §5.1, Footnote 10.
* H. Matsumura, *Commutative Ring Theory*, second edition, Cambridge University Press, 1989, §26.
* The Stacks Project, Algebra, Definition 15.47.1 (Tag 07P1) and Lemma 15.47.2 (Tag 07P2).
-/

public section

noncomputable section

open KaehlerDifferential

namespace TauCeti

section KaehlerTheorems

variable {p : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [Field k] [ExpChar k p] [Algebra R k]
variable {ι : Type*}

/-- The differentials `{D R k (b i)}` of a `p`-basis `b : ι → k` form a `k`-basis of `Ω[k⁄R]`,
for any base ring `R` whose image lies in `k ^ p`. -/
def IsPBasis.kaehlerBasis {b : ι → k} (hb : IsPBasis p b)
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) :
    Module.Basis ι k Ω[k⁄R] :=
  let φ : ι → Module.Dual k Ω[k⁄R] := fun j ↦
    (hb.coordDerivation j).liftKaehlerDifferential.comp
      (kaehlerEquivFrobeniusRange p R k hR).toLinearMap
  have hlin : LinearIndependent k (fun i ↦ D R k (b i)) :=
    LinearIndependent.of_pairwise_dual_eq_zero_one (fun i ↦ D R k (b i)) φ
      (fun i j hij ↦ by simp [φ, hij.symm])
      (fun i ↦ by simp [φ])
  have hspan : Submodule.span k (Set.range fun i ↦ D R k (b i)) = ⊤ := by
    rw [eq_top_iff, ← span_range_derivation R k, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    refine (D R k).map_mem_span_of_mem_adjoin (p := p) b ?_
    rw [hb.adjoin_eq_top]
    exact IntermediateField.mem_top
  Module.Basis.mk hlin hspan.ge

/-- Evaluating `IsPBasis.kaehlerBasis` at `i` gives the differential `D R k (b i)`. -/
@[simp]
theorem IsPBasis.kaehlerBasis_apply {b : ι → k} (hb : IsPBasis p b)
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (i : ι) :
    hb.kaehlerBasis hR i = D R k (b i) := by
  rw [IsPBasis.kaehlerBasis, Module.Basis.coe_mk]

/-- Evaluating an `R`-derivation out of `k` on a `p`-basis `b : ι → k` gives a `k`-linear
equivalence `Derivation R k M ≃ₗ[k] (ι → M)` whenever the image of `R` lies in `k ^ p`. -/
def IsPBasis.derivationEquiv {b : ι → k} (hb : IsPBasis p b)
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange)
    {M : Type*} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower R k M] :
    Derivation R k M ≃ₗ[k] (ι → M) :=
  (KaehlerDifferential.linearMapEquivDerivation (R := R) (S := k)).symm.trans
    ((hb.kaehlerBasis hR).constr k).symm

/-- The forward map of `IsPBasis.derivationEquiv` evaluates a derivation at each member of `b`. -/
@[simp]
theorem IsPBasis.derivationEquiv_apply {b : ι → k} (hb : IsPBasis p b)
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange)
    {M : Type*} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower R k M]
    (d : Derivation R k M) (i : ι) :
    hb.derivationEquiv hR d i = d (b i) := by
  simp [IsPBasis.derivationEquiv]

/-- The inverse map of `IsPBasis.derivationEquiv` constructs the unique derivation taking prescribed
values on the `p`-basis `b`. -/
@[simp]
theorem IsPBasis.derivationEquiv_symm_apply {b : ι → k} (hb : IsPBasis p b)
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange)
    {M : Type*} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower R k M]
    (v : ι → M) (i : ι) :
    ((hb.derivationEquiv hR).symm v) (b i) = v i := by
  dsimp [IsPBasis.derivationEquiv]
  rw [KaehlerDifferential.linearMapEquivDerivation_apply_apply, ← hb.kaehlerBasis_apply hR i,
    Module.Basis.constr_basis]

/-- If the Kähler differentials `{D R k (b i)}` are linearly independent over `k`, then `b` is
`p`-independent (without requiring the image of `R` to lie in `k ^ p`). -/
theorem isPIndependent_of_linearIndependent_D {b : ι → k}
    (hlin : LinearIndependent k (fun i ↦ D R k (b i))) : IsPIndependent p b := by
  by_contra hnot
  obtain ⟨i, hi⟩ := exists_mem_adjoin_image_compl_singleton_of_not_isPIndependent hnot
  have hmem := (D R k).map_mem_span_of_mem_adjoin (fun j : ({i}ᶜ : Set ι) ↦ b j)
    ((Set.image_eq_range b ({i}ᶜ : Set ι)).symm ▸ hi)
  rw [← Set.image_eq_range (fun j ↦ D R k (b j)) ({i}ᶜ : Set ι)] at hmem
  exact hlin.notMem_span_image (Set.notMem_compl_iff.mpr rfl) hmem

/-- A family in a field `k` of prime characteristic `p` is `p`-independent if and only if its
Kähler differentials over `R` are linearly independent over `k`, for any base ring `R` whose
image lies in `k ^ p`. -/
theorem isPIndependent_iff_linearIndependent_D
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (b : ι → k) :
    IsPIndependent p b ↔ LinearIndependent k (fun i ↦ D R k (b i)) := by
  refine ⟨fun hb ↦ ?_, isPIndependent_of_linearIndependent_D⟩
  let e : ι ≃ Set.range b := Equiv.ofInjective b hb.injective
  have hrange : IsPIndependent p ((↑) : Set.range b → k) := by
    have hcomp : (((↑) : Set.range b → k) ∘ e) = b :=
      funext fun i ↦ congrArg Subtype.val (Equiv.ofInjective_apply b hb.injective i)
    exact (isPIndependent_equiv ((↑) : Set.range b → k) e).mp (hcomp.symm ▸ hb)
  obtain ⟨t, hsub, ht⟩ := exists_isPBasis_of_isPIndependent hrange
  let f : ι → t := fun i ↦ ⟨b i, hsub ⟨i, rfl⟩⟩
  have hf : Function.Injective f := fun i j h ↦ hb.injective (congrArg Subtype.val h)
  have hcoe : (fun i ↦ D R k (b i)) = (ht.kaehlerBasis hR) ∘ f :=
    funext fun i ↦ (ht.kaehlerBasis_apply hR (f i)).symm
  rw [hcoe]
  exact (ht.kaehlerBasis hR).linearIndependent.comp f hf

/-- A family in a field `k` of prime characteristic `p` is a `p`-basis if and only if its
Kähler differentials over `R` are linearly independent and span `Ω[k⁄R]`, for any base ring `R`
whose image lies in `k ^ p`. -/
theorem isPBasis_iff_linearIndependent_and_span_D
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (b : ι → k) :
    IsPBasis p b ↔
      LinearIndependent k (fun i ↦ D R k (b i)) ∧
        Submodule.span k (Set.range fun i ↦ D R k (b i)) = ⊤ := by
  constructor
  · intro hb
    have hcoe : (fun i ↦ D R k (b i)) = ⇑(hb.kaehlerBasis hR) :=
      funext fun i ↦ (hb.kaehlerBasis_apply hR i).symm
    rw [hcoe]
    exact ⟨(hb.kaehlerBasis hR).linearIndependent, (hb.kaehlerBasis hR).span_eq⟩
  · rintro ⟨hlin, hspan⟩
    have hind : IsPIndependent p b := isPIndependent_of_linearIndependent_D hlin
    refine (isPBasis_iff b).mpr ⟨hind, (span_range_pMonomial_eq_top_iff b).mpr ?_⟩
    rw [eq_top_iff]
    intro x _
    by_contra hx
    have hopt : IsPIndependent p (Option.elim' x b) := (isPIndependent_option_iff hind x).mpr hx
    have hopt_lin : LinearIndependent k (fun o ↦ D R k (Option.elim' x b o)) :=
      (isPIndependent_iff_linearIndependent_D hR _).mp hopt
    have hnotmem := hopt_lin.notMem_span_image (s := Set.range Option.some) (x := none) (by simp)
    rw [← Set.range_comp', show (fun i ↦ D R k (Option.elim' x b (Option.some i))) =
      fun i ↦ D R k (b i) from rfl, hspan] at hnotmem
    exact hnotmem Submodule.mem_top

/-- In a field `k` of prime characteristic `p`, the kernel of the universal derivation
`D R k : k → Ω[k⁄R]` is the Frobenius subfield `k ^ p`, for any base ring `R` whose image lies in
`k ^ p`. -/
theorem D_eq_zero_iff_mem_fieldRange_frobenius
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (x : k) :
    D R k x = 0 ↔ x ∈ (frobenius k p).fieldRange := by
  refine ⟨fun hx ↦ ?_, (D R k).map_eq_zero_of_mem_fieldRange_frobenius⟩
  by_contra hnot
  have hnot_adjoin :
      x ∉ IntermediateField.adjoin (frobenius k p).fieldRange
        (Set.range (Empty.elim : Empty → k)) := by
    rw [Set.range_eq_empty, IntermediateField.adjoin_empty, IntermediateField.mem_bot]
    rintro ⟨c, hc⟩
    exact hnot (hc ▸ c.property)
  have hopt : IsPIndependent p (Option.elim' x (Empty.elim : Empty → k)) :=
    (isPIndependent_option_iff (isPIndependent_empty _) x).mpr hnot_adjoin
  have hlin := (isPIndependent_iff_linearIndependent_D hR _).mp hopt
  exact hlin.ne_zero none (by simpa using hx)

/-- **Finiteness criterion for differentials**: without assuming `[k : k ^ p]` finite, `Ω[k⁄R]` is
finite-dimensional over `k` if and only if `k` is finite-dimensional over its Frobenius subfield
`k ^ p`, for any base ring `R` whose image lies in `k ^ p`. -/
theorem finiteDimensional_kaehlerDifferential_iff (p : ℕ) [Fact p.Prime] (R k : Type*)
    [CommRing R] [Field k] [ExpChar k p] [Algebra R k]
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) :
    FiniteDimensional k Ω[k⁄R] ↔ FiniteDimensional (frobenius k p).fieldRange k := by
  obtain ⟨t, ht⟩ := exists_isPBasis p k
  rw [← ht.finite_iff_finiteDimensional]
  constructor
  · intro hfd
    have : Fintype t := FiniteDimensional.fintypeBasisIndex (ht.kaehlerBasis hR)
    exact Finite.of_fintype t
  · intro hfin
    have : Fintype t := Fintype.ofFinite t
    exact Module.Finite.of_basis (ht.kaehlerBasis hR)

/-- **Degree-dimension formula**: when a field `k` of prime characteristic `p` is finite-dimensional
over its Frobenius subfield `k ^ p`, `[k : k ^ p] = p ^ dim_k Ω[k⁄R]` for any base ring `R` whose
image lies in `k ^ p`. -/
theorem finrank_fieldRange_frobenius_eq_pow_finrank_kaehlerDifferential (p : ℕ) [Fact p.Prime]
    (R k : Type*) [CommRing R] [Field k] [ExpChar k p] [Algebra R k]
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange)
    [FiniteDimensional (frobenius k p).fieldRange k] :
    Module.finrank (frobenius k p).fieldRange k = p ^ Module.finrank k Ω[k⁄R] := by
  obtain ⟨t, ht⟩ := exists_isPBasis p k
  have hfin : Finite t := ht.finite_iff_finiteDimensional.mpr ‹_›
  have : Fintype t := Fintype.ofFinite t
  rw [ht.finrank_fieldRange_frobenius, Nat.card_eq_fintype_card,
    Module.finrank_eq_card_basis (ht.kaehlerBasis hR)]

/-- A field `k` of prime characteristic `p` has vanishing Kähler differentials `Ω[k⁄R]` if and
only if `k` is perfect, for any base ring `R` whose image lies in `k ^ p`. -/
theorem subsingleton_kaehlerDifferential_iff_perfectRing (p : ℕ) [Fact p.Prime] (R k : Type*)
    [CommRing R] [Field k] [ExpChar k p] [Algebra R k]
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) :
    Subsingleton Ω[k⁄R] ↔ PerfectRing k p := by
  constructor
  · intro _
    refine PerfectRing.ofSurjective k p fun x ↦ ?_
    exact (D_eq_zero_iff_mem_fieldRange_frobenius hR x).mp (Subsingleton.elim _ _)
  · intro hperf
    have hb : IsPBasis p (Empty.elim : Empty → k) :=
      (isPBasis_empty_iff_perfectRing _).mpr hperf
    exact (hb.kaehlerBasis hR).repr.toEquiv.subsingleton

end KaehlerTheorems

section DualDerivation

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [ExpChar k p] {ι : Type*}

/-- The coordinate derivation `hb.coordDerivation j` equals the derivation dual to
`hb.kaehlerBasis` over the Frobenius subfield `k ^ p`. -/
theorem IsPBasis.coordDerivation_eq_dualDerivation {b : ι → k} (hb : IsPBasis p b) (j : ι) :
    hb.coordDerivation j =
      (hb.kaehlerBasis (fun c : (frobenius k p).fieldRange ↦ c.property)).dualDerivation j := by
  classical
  refine hb.derivation_ext fun i ↦ ?_
  rw [(hb.kaehlerBasis fun c : (frobenius k p).fieldRange ↦
    c.property).dualDerivation_apply_of_kaehlerD_eq
      (fun m ↦ (hb.kaehlerBasis_apply (fun c ↦ c.property) m).symm)]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

end DualDerivation

end TauCeti

end
