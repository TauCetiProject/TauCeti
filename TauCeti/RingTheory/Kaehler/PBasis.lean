/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.PBasis
public import TauCeti.RingTheory.Kaehler.Frobenius

/-!
# `p`-bases and Kähler differentials

Let `k` be a field of prime characteristic `p` and `R` a commutative ring with an algebra map into
`k` whose image lies in the Frobenius subfield `k ^ p = (frobenius k p).fieldRange` (for instance,
`R = ℤ`, `R = ZMod p`, `R = k ^ p`, or any perfect ring `R` of characteristic `p`).

Every `R`-derivation out of `k` vanishes on `k ^ p`, so `Ω[k⁄R]` is canonically isomorphic to
`Ω[k⁄k ^ p]`. From a `p`-basis `b : ι → k`, the coordinate `k ^ p`-derivations
`hb.coordDerivation j` lift to dual forms on `Ω[k⁄R]`, showing that `D R k ∘ b` is a `k`-basis of
`Ω[k⁄R]`. Combining this with the existence of possibly infinite `p`-bases yields the equivalences
between `p`-independence and `k`-linear independence of differentials, between `p`-bases and
`k`-bases of `Ω[k⁄R]`, the kernel identification `ker (D R k) = k ^ p`, the finiteness criterion
`FiniteDimensional k Ω[k⁄R] ↔ FiniteDimensional (frobenius k p).fieldRange k`, and the degree
formula `[k : k ^ p] = p ^ dim_k Ω[k⁄R]` when `[k : k ^ p]` is finite.

## Main definitions

* `TauCeti.IsPBasis.kaehlerBasis`: the `k`-basis `i ↦ D R k (b i)` of `Ω[k⁄R]` associated to a
  `p`-basis `b`.

## Main results

* `TauCeti.derivation_mem_span_of_mem_adjoin`, `TauCeti.D_mem_span_D_of_mem_adjoin`: derivatives
  on `k ^ p(range b)` lie in the `k`-span of the derivatives of `b`.
* `TauCeti.IsPBasis.derivation_ext`: two `R`-derivations out of `k` into a `k`-module that agree
  on a `p`-basis are equal.
* `TauCeti.isPIndependent_of_linearIndependent_D`,
  `TauCeti.isPIndependent_iff_linearIndependent_D`: a family is `p`-independent iff its
  differentials are linearly independent over `k`.
* `TauCeti.isPBasis_iff_linearIndependent_and_span_D`: a family is a `p`-basis iff its
  differentials form a `k`-basis of `Ω[k⁄R]`.
* `TauCeti.D_eq_zero_iff_mem_fieldRange_frobenius`: `D R k x = 0 ↔ x ∈ (frobenius k p).fieldRange`.
* `TauCeti.kaehler_finiteDimensional_iff`: `Ω[k⁄R]` is finite-dimensional over `k` iff `k` is
  finite-dimensional over `k ^ p`.
* `TauCeti.finrank_fieldRange_frobenius_eq_pow_finrank_kaehler`:
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

/-- For any family `b : ι → k` and any `R`-derivation `d : Derivation R k M` into a `k`-module,
every element of the intermediate field `k ^ p(range b)` has derivative in the `k`-linear span of
`{d (b i)}`. -/
theorem derivation_mem_span_of_mem_adjoin {M : Type*} [AddCommMonoid M] [Module R M] [Module k M]
    (d : Derivation R k M) (b : ι → k) {x : k}
    (hx : x ∈ IntermediateField.adjoin (frobenius k p).fieldRange (Set.range b)) :
    d x ∈ Submodule.span k (Set.range fun i ↦ d (b i)) := by
  set S : Submodule k M := Submodule.span k (Set.range fun i ↦ d (b i))
  rw [← IntermediateField.mem_toSubalgebra, ← Subalgebra.mem_toSubmodule,
    ← span_range_pMonomial_eq_adjoin] at hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨e, rfl⟩ := hu
    rw [pMonomial_def, Finsupp.prod]
    induction e.support using Finset.cons_induction with
    | empty => simp
    | cons i s hi ih =>
      rw [Finset.prod_cons, d.leibniz]
      refine S.add_mem (S.smul_mem _ ih) (S.smul_mem _ ?_)
      rw [d.leibniz_pow, ← Nat.cast_smul_eq_nsmul k]
      exact S.smul_mem _ (S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact S.add_mem hu hv
  | smul c u _ hu =>
    rw [Subfield.smul_def, smul_eq_mul, d.leibniz,
      d.map_eq_zero_of_mem_fieldRange_frobenius c.property, smul_zero, add_zero]
    exact S.smul_mem (c : k) hu

/-- For any family `b : ι → k`, every element of the intermediate field `k ^ p(range b)` has
differential in the `k`-linear span of `{D R k (b i)}`. -/
theorem D_mem_span_D_of_mem_adjoin (b : ι → k) {x : k}
    (hx : x ∈ IntermediateField.adjoin (frobenius k p).fieldRange (Set.range b)) :
    D R k x ∈ Submodule.span k (Set.range fun i ↦ D R k (b i)) :=
  derivation_mem_span_of_mem_adjoin (D R k) b hx

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
    refine D_mem_span_D_of_mem_adjoin (p := p) b ?_
    rw [hb.adjoin_eq_top]
    exact IntermediateField.mem_top
  Module.Basis.mk hlin hspan.ge

/-- Evaluating `IsPBasis.kaehlerBasis` at `i` gives the differential `D R k (b i)`. -/
@[simp]
theorem IsPBasis.kaehlerBasis_apply {b : ι → k} (hb : IsPBasis p b)
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (i : ι) :
    hb.kaehlerBasis hR i = D R k (b i) := by
  rw [IsPBasis.kaehlerBasis, Module.Basis.coe_mk]

/-- Two `R`-derivations out of `k` into a `k`-module that agree on a `p`-basis `b` are equal. -/
theorem IsPBasis.derivation_ext {b : ι → k} (hb : IsPBasis p b) {M : Type*} [AddCommGroup M]
    [Module R M] [Module k M] {d₁ d₂ : Derivation R k M} (h : ∀ i, d₁ (b i) = d₂ (b i)) :
    d₁ = d₂ := by
  have : IsScalarTower (frobenius k p).fieldRange k M :=
    ⟨fun c x m ↦ by rw [Subfield.smul_def, Subfield.smul_def, smul_eq_mul, smul_smul]⟩
  let promote (d : Derivation R k M) : Derivation (frobenius k p).fieldRange k M :=
    { toLinearMap :=
        { toFun := d
          map_add' := d.map_add
          map_smul' := fun c x ↦ by
            rw [RingHom.id_apply, Subfield.smul_def, smul_eq_mul, d.leibniz,
              d.map_eq_zero_of_mem_fieldRange_frobenius c.property, smul_zero, add_zero,
              ← Subfield.smul_def] }
      map_one_eq_zero' := d.map_one_eq_zero
      leibniz' := d.leibniz }
  let B : Module.Basis ι k Ω[k⁄(frobenius k p).fieldRange] := hb.kaehlerBasis (fun c ↦ c.property)
  have hlift : (promote d₁).liftKaehlerDifferential = (promote d₂).liftKaehlerDifferential :=
    B.ext fun i ↦ by
      dsimp only [B]
      rw [hb.kaehlerBasis_apply (fun c ↦ c.property) i,
        Derivation.liftKaehlerDifferential_comp_D (promote d₁),
        Derivation.liftKaehlerDifferential_comp_D (promote d₂)]
      exact h i
  ext x
  calc
    d₁ x = (promote d₁).liftKaehlerDifferential (D (frobenius k p).fieldRange k x) := by
      rw [Derivation.liftKaehlerDifferential_comp_D (promote d₁)]; rfl
    _ = (promote d₂).liftKaehlerDifferential (D (frobenius k p).fieldRange k x) :=
      LinearMap.congr_fun hlift _
    _ = d₂ x := by
      rw [Derivation.liftKaehlerDifferential_comp_D (promote d₂)]; rfl

/-- If the Kähler differentials `{D R k (b i)}` are linearly independent over `k`, then `b` is
`p`-independent (without requiring the image of `R` to lie in `k ^ p`). -/
theorem isPIndependent_of_linearIndependent_D {b : ι → k}
    (hlin : LinearIndependent k (fun i ↦ D R k (b i))) : IsPIndependent p b := by
  by_contra hnot
  obtain ⟨i, hi⟩ := exists_mem_adjoin_image_compl_singleton_of_not_isPIndependent hnot
  have hbrange : Set.range (fun j : ({i}ᶜ : Set ι) ↦ b j) = b '' ({i}ᶜ : Set ι) := by
    ext y; simp
  have hmem := D_mem_span_D_of_mem_adjoin (R := R) (fun j : ({i}ᶜ : Set ι) ↦ b j)
    (hbrange.symm ▸ hi)
  have hrange : Set.range (fun j : ({i}ᶜ : Set ι) ↦ D R k (b j)) =
      (fun j ↦ D R k (b j)) '' ({i}ᶜ : Set ι) := by
    ext ω
    simp
  rw [hrange] at hmem
  exact hlin.notMem_span_image (Set.notMem_compl_iff.mpr rfl) hmem

/-- A family in a field `k` of prime characteristic `p` is `p`-independent if and only if its
Kähler differentials over `R` are linearly independent over `k`, for any base ring `R` whose
image lies in `k ^ p`. -/
theorem isPIndependent_iff_linearIndependent_D
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (b : ι → k) :
    IsPIndependent p b ↔ LinearIndependent k (fun i ↦ D R k (b i)) := by
  refine ⟨fun hb ↦ ?_, isPIndependent_of_linearIndependent_D⟩
  let e : ι ≃ Set.range b := Equiv.ofBijective (fun i ↦ ⟨b i, i, rfl⟩)
    ⟨fun i j h ↦ hb.injective (congrArg Subtype.val h), fun ⟨_, i, hi⟩ ↦ ⟨i, Subtype.ext hi⟩⟩
  have hrange : IsPIndependent p ((↑) : Set.range b → k) := by
    have hcomp : (((↑) : Set.range b → k) ∘ e) = b := rfl
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
    have himg : (fun o ↦ D R k (Option.elim' x b o)) '' Set.range Option.some =
        Set.range (fun i ↦ D R k (b i)) := by
      ext ω
      simp
    rw [himg, hspan] at hnotmem
    exact hnotmem Submodule.mem_top

/-- In a field `k` of prime characteristic `p`, the kernel of the universal derivation
`D R k : k → Ω[k⁄R]` is the Frobenius subfield `k ^ p`, for any base ring `R` whose image lies in
`k ^ p`. -/
theorem D_eq_zero_iff_mem_fieldRange_frobenius
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (x : k) :
    D R k x = 0 ↔ x ∈ (frobenius k p).fieldRange := by
  refine ⟨fun hx ↦ ?_, D_eq_zero_of_mem_fieldRange_frobenius⟩
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
theorem kaehler_finiteDimensional_iff (p : ℕ) [Fact p.Prime] (R k : Type*)
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
theorem finrank_fieldRange_frobenius_eq_pow_finrank_kaehler (p : ℕ) [Fact p.Prime] (R k : Type*)
    [CommRing R] [Field k] [ExpChar k p] [Algebra R k]
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

end TauCeti

end
