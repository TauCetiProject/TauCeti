/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import TauCeti.RingTheory.Kaehler.PBasis
import Mathlib.FieldTheory.IsPerfectClosure
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import TauCeti.FieldTheory.Frobenius.Range
import TauCeti.FieldTheory.FunctionField.Differential.Kaehler

/-!
# Examples of `p`-bases and Kähler differentials in prime characteristic

* **Perfect fields:** for any perfect field `k` of prime characteristic `p`, the empty family is a
  `p`-basis, `Ω[k⁄ZMod p]` vanishes, `[k : k ^ p] = 1`, and `dim_k Ω[k⁄ZMod p] = 0`.
* **Rational function field `𝔽_p(t)`:** `RatFunc.X` is a singleton `p`-basis of `RatFunc (ZMod p)`,
  `[𝔽_p(t) : 𝔽_p(t ^ p)] = p`, `D (ZMod p) _ RatFunc.X` spans `Ω[𝔽_p(t)⁄𝔽_p]`, and
  `dim Ω[𝔽_p(t)⁄𝔽_p] = 1`, including the case `p = 2`.
* **Transcendence basis failing to be a `p`-basis:** in `RatFunc (ZMod p)`, `{RatFunc.X ^ p}` is a
  transcendence basis over `ZMod p`, yet it is not a `p`-basis (`RatFunc.X ^ p ∈ k ^ p`) and its
  differential vanishes.
* **Countably infinite pure transcendental extension:** for
  `k = FractionRing (MvPolynomial ℕ (ZMod p))`, the indeterminates form an infinite `p`-basis,
  their differentials form an infinite `k`-basis of `Ω[k⁄ZMod p]`, and both
  `FiniteDimensional (frobenius k p).fieldRange k` and `FiniteDimensional k Ω[k⁄ZMod p]` fail.
* **Perfect closure of an infinite transcendental extension:** the perfect closure of
  `FractionRing (MvPolynomial ℕ (ZMod p))` has transcendence degree `ℵ₀` over `ZMod p`, yet it is
  perfect with empty `p`-basis, `Ω¹ = 0`, `[L : L ^ p] = 1 = p ^ 0`, and `dim_L Ω¹ = 0`.

The rational-function example specializes `TauCeti.kaehlerBasisRatFunc`, while the
polynomial-fraction-field example identifies `Ω[K⁄ZMod p]` by transporting Mathlib's polynomial
differential basis `KaehlerDifferential.mvPolynomialBasis` along
`KaehlerDifferential.isBaseChange_of_formallyEtale` via `IsBaseChange.basis`.
-/

namespace TauCeti.Examples

open KaehlerDifferential TauCeti

private theorem perfectRing_summary (p : ℕ) [Fact p.Prime] (k : Type*)
    [Field k] [ExpChar k p] [PerfectRing k p] [Algebra (ZMod p) k] :
    IsPBasis p (Empty.elim : Empty → k) ∧
      Subsingleton Ω[k⁄ZMod p] ∧
      FiniteDimensional (frobenius k p).fieldRange k ∧
      FiniteDimensional k Ω[k⁄ZMod p] ∧
      Module.finrank (frobenius k p).fieldRange k = 1 ∧
      Module.finrank k Ω[k⁄ZMod p] = 0 := by
  have hb : IsPBasis p (Empty.elim : Empty → k) :=
    (isPBasis_empty_iff_perfectRing (Empty.elim : Empty → k)).mpr ‹_›
  have hsub : Subsingleton Ω[k⁄ZMod p] :=
    (subsingleton_kaehlerDifferential_iff_perfectRing p (ZMod p) k
      (algebraMap_mem_fieldRange_frobenius_of_perfectRing p)).mpr ‹_›
  have hfd_frob : FiniteDimensional (frobenius k p).fieldRange k :=
    hb.finite_iff_finiteDimensional.mp inferInstance
  have hfd_kaehler : FiniteDimensional k Ω[k⁄ZMod p] :=
    (finiteDimensional_kaehlerDifferential_iff p (ZMod p) k
      (algebraMap_mem_fieldRange_frobenius_of_perfectRing p)).mpr hfd_frob
  refine ⟨hb, hsub, hfd_frob, hfd_kaehler, ?_, Module.finrank_zero_of_subsingleton⟩
  simpa using hb.finrank_fieldRange_frobenius

-- For a perfect field of prime characteristic `p`, the empty family is a `p`-basis,
-- `Ω[k⁄ZMod p]` vanishes, `[k : k ^ p] = 1`, and `dim_k Ω[k⁄ZMod p] = 0`.
example (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectField k]
    [Algebra (ZMod p) k] :
    IsPBasis p (Empty.elim : Empty → k) ∧
      Subsingleton Ω[k⁄ZMod p] ∧
      Module.finrank (frobenius k p).fieldRange k = 1 ∧
      Module.finrank k Ω[k⁄ZMod p] = 0 := by
  have : PerfectRing k p := PerfectField.toPerfectRing p
  obtain ⟨hb, hsub, -, -, hfinrank, homega⟩ := perfectRing_summary p k
  exact ⟨hb, hsub, hfinrank, homega⟩

-- In `RatFunc (ZMod p)`, `RatFunc.X` forms a `p`-basis, `[𝔽_p(t) : 𝔽_p(t ^ p)] = p`,
-- `D (ZMod p) _ RatFunc.X` spans `Ω¹`, and `dim Ω¹ = 1`, including `p = 2`.
example :
    (∀ (p : ℕ) [Fact p.Prime],
      IsPBasis p (fun _ : Fin 1 ↦ (RatFunc.X : RatFunc (ZMod p))) ∧
        Module.finrank (frobenius (RatFunc (ZMod p)) p).fieldRange (RatFunc (ZMod p)) = p ∧
        Submodule.span (RatFunc (ZMod p))
          {D (ZMod p) (RatFunc (ZMod p)) (RatFunc.X : RatFunc (ZMod p))} = ⊤ ∧
        Module.finrank (RatFunc (ZMod p)) Ω[RatFunc (ZMod p)⁄ZMod p] = 1) ∧
    (IsPBasis 2 (fun _ : Fin 1 ↦ (RatFunc.X : RatFunc (ZMod 2))) ∧
      Module.finrank (frobenius (RatFunc (ZMod 2)) 2).fieldRange (RatFunc (ZMod 2)) = 2 ∧
      Submodule.span (RatFunc (ZMod 2))
        {D (ZMod 2) (RatFunc (ZMod 2)) (RatFunc.X : RatFunc (ZMod 2))} = ⊤ ∧
      Module.finrank (RatFunc (ZMod 2)) Ω[RatFunc (ZMod 2)⁄ZMod 2] = 1) := by
  have h : ∀ (p : ℕ) [Fact p.Prime],
      IsPBasis p (fun _ : Fin 1 ↦ (RatFunc.X : RatFunc (ZMod p))) ∧
        Module.finrank (frobenius (RatFunc (ZMod p)) p).fieldRange (RatFunc (ZMod p)) = p ∧
        Submodule.span (RatFunc (ZMod p))
          {D (ZMod p) (RatFunc (ZMod p)) (RatFunc.X : RatFunc (ZMod p))} = ⊤ ∧
        Module.finrank (RatFunc (ZMod p)) Ω[RatFunc (ZMod p)⁄ZMod p] = 1 := by
    intro p _
    let K := RatFunc (ZMod p)
    let bK : Module.Basis (Fin 1) K Ω[K⁄ZMod p] :=
      (kaehlerBasisRatFunc (ZMod p)).reindex (Equiv.ofUnique Unit (Fin 1))
    have hbK : ∀ i : Fin 1, bK i = D (ZMod p) K (RatFunc.X : K) := fun i ↦ by
      dsimp only [bK]
      rw [Module.Basis.coe_reindex, Function.comp_apply, kaehlerBasisRatFunc_apply]
    have hfun : (fun _ : Fin 1 ↦ D (ZMod p) K (RatFunc.X : K)) = ⇑bK := funext fun i ↦ (hbK i).symm
    have hb : IsPBasis p (fun _ : Fin 1 ↦ (RatFunc.X : K)) := by
      rw [isPBasis_iff_linearIndependent_and_span_D (R := ZMod p)
        (algebraMap_mem_fieldRange_frobenius_of_perfectRing p), hfun]
      exact ⟨bK.linearIndependent, bK.span_eq⟩
    have hspan : Submodule.span K {D (ZMod p) K (RatFunc.X : K)} = ⊤ := by
      have h := bK.span_eq
      rwa [← hfun, Set.range_const] at h
    refine ⟨hb, by simpa using hb.finrank_fieldRange_frobenius, hspan, ?_⟩
    simpa using Module.finrank_eq_card_basis bK
  exact ⟨h, h 2⟩

-- In `RatFunc (ZMod p)`, `{RatFunc.X ^ p}` is a transcendence basis over `ZMod p`, yet it is not a
-- `p`-basis (since `RatFunc.X ^ p ∈ k ^ p`) and `D (ZMod p) _ (RatFunc.X ^ p) = 0`.
example (p : ℕ) [Fact p.Prime] :
    let b : Fin 1 → RatFunc (ZMod p) := fun _ ↦ (RatFunc.X : RatFunc (ZMod p)) ^ p
    IsTranscendenceBasis (ZMod p) b ∧
      ¬ IsPBasis p b ∧
      (RatFunc.X : RatFunc (ZMod p)) ^ p ∈ (frobenius (RatFunc (ZMod p)) p).fieldRange ∧
      D (ZMod p) (RatFunc (ZMod p)) ((RatFunc.X : RatFunc (ZMod p)) ^ p) = 0 := by
  intro b
  let S := Polynomial (ZMod p)
  let K := RatFunc (ZMod p)
  have hmem : (RatFunc.X : K) ^ p ∈ (frobenius K p).fieldRange := ⟨RatFunc.X, frobenius_def ..⟩
  have hD : D (ZMod p) K ((RatFunc.X : K) ^ p) = 0 :=
    (D (ZMod p) K).map_eq_zero_of_mem_fieldRange_frobenius hmem
  have hnot : ¬ IsPBasis p b := fun hb ↦
    ((isPIndependent_iff_linearIndependent_D (R := ZMod p)
      (algebraMap_mem_fieldRange_frobenius_of_perfectRing p) b).mp hb.isPIndependent).ne_zero 0 hD
  have : Algebra.IsAlgebraic S K := IsLocalization.isAlgebraic K (nonZeroDivisors S)
  have htb := (IsTranscendenceBasis.polynomial Unit (ZMod p)).algebraMap_comp (A := K)
  have htrK : Algebra.trdeg (ZMod p) (RatFunc (ZMod p)) = 1 := by
    simpa using htb.cardinalMk_eq_trdeg.symm
  have htrX : Transcendental (ZMod p) (RatFunc.X : K) :=
    algebraicIndependent_unique_type_iff.mp htb.1
  have hind : AlgebraicIndependent (ZMod p) b :=
    (algebraicIndependent_singleton_iff (0 : Fin 1)).mpr (htrX.pow (Fact.out : p.Prime).pos)
  exact ⟨hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simp [htrK]), hnot, hmem, hD⟩

-- For `k = FractionRing (MvPolynomial ℕ (ZMod p))`, the indeterminates form an infinite `p`-basis,
-- their differentials form an infinite `k`-basis of `Ω[k⁄ZMod p]`, and both `[k : k ^ p]` and
-- `dim_k Ω[k⁄ZMod p]` are infinite.
example (p : ℕ) [Fact p.Prime] :
    let K := FractionRing (MvPolynomial ℕ (ZMod p))
    have : CharP K p := charP_of_injective_algebraMap
      (IsFractionRing.injective (MvPolynomial ℕ (ZMod p)) K) p
    let b : ℕ → K := fun n ↦ algebraMap (MvPolynomial ℕ (ZMod p)) K (MvPolynomial.X n)
    IsPBasis p b ∧
      LinearIndependent K (fun n : ℕ ↦ D (ZMod p) K (b n)) ∧
      Submodule.span K (Set.range fun n : ℕ ↦ D (ZMod p) K (b n)) = ⊤ ∧
      ¬ FiniteDimensional (frobenius K p).fieldRange K ∧
      ¬ FiniteDimensional K Ω[K⁄ZMod p] := by
  intro K hchar b
  let S := MvPolynomial ℕ (ZMod p)
  have : Algebra.FormallyEtale S K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors S)
  have hbc : IsBaseChange K (KaehlerDifferential.map (ZMod p) (ZMod p) S K) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale (ZMod p) S K
  let bK : Module.Basis ℕ K Ω[K⁄ZMod p] :=
    hbc.basis (KaehlerDifferential.mvPolynomialBasis (ZMod p) ℕ)
  have hbK : ∀ n : ℕ, bK n = D (ZMod p) K (b n) := fun n ↦ by
    rw [hbc.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
  have hfun : (fun n : ℕ ↦ D (ZMod p) K (b n)) = ⇑bK := funext fun n ↦ (hbK n).symm
  have hb : IsPBasis p b := by
    rw [isPBasis_iff_linearIndependent_and_span_D (R := ZMod p)
      (algebraMap_mem_fieldRange_frobenius_of_perfectRing p), hfun]
    exact ⟨bK.linearIndependent, bK.span_eq⟩
  have hnot_frob : ¬ FiniteDimensional (frobenius K p).fieldRange K := fun hfd ↦
    have : Finite ℕ := hb.finite_iff_finiteDimensional.mpr hfd
    not_finite ℕ
  have hnot_kaehler : ¬ FiniteDimensional K Ω[K⁄ZMod p] := fun hfd ↦
    hnot_frob ((finiteDimensional_kaehlerDifferential_iff p (ZMod p) K
      (algebraMap_mem_fieldRange_frobenius_of_perfectRing p)).mp hfd)
  exact ⟨hb, hfun ▸ bK.linearIndependent, hfun ▸ bK.span_eq, hnot_frob, hnot_kaehler⟩

/-- The perfect closure `L` of `FractionRing (MvPolynomial ℕ (ZMod p))` has transcendence degree
`ℵ₀` over `ZMod p`, yet it is perfect with empty `p`-basis, `Ω[L⁄ZMod p] = 0`,
`[L : L ^ p] = 1 = p ^ 0`, and `dim_L Ω[L⁄ZMod p] = 0`. -/
public theorem perfectClosure_mvPolynomial_pBasis (p : ℕ) [Fact p.Prime] :
    let K := FractionRing (MvPolynomial ℕ (ZMod p))
    have : CharP K p := charP_of_injective_algebraMap
      (IsFractionRing.injective (MvPolynomial ℕ (ZMod p)) K) p
    let L := PerfectClosure K p
    letI : Algebra (ZMod p) L := ((PerfectClosure.of K p).comp (algebraMap (ZMod p) K)).toAlgebra
    Algebra.trdeg (ZMod p) L = Cardinal.aleph0 ∧
      IsPBasis p (Empty.elim : Empty → L) ∧
      Subsingleton Ω[L⁄ZMod p] ∧
      FiniteDimensional (frobenius L p).fieldRange L ∧
      FiniteDimensional L Ω[L⁄ZMod p] ∧
      Module.finrank (frobenius L p).fieldRange L = 1 ∧
      Module.finrank L Ω[L⁄ZMod p] = 0 := by
  intro K hchar L
  let : Algebra (ZMod p) L := ((PerfectClosure.of K p).comp (algebraMap (ZMod p) K)).toAlgebra
  let : Algebra K L := (PerfectClosure.of K p).toAlgebra
  have hof : algebraMap K L = PerfectClosure.of K p :=
    RingHom.algebraMap_toAlgebra (PerfectClosure.of K p)
  have : IsScalarTower (ZMod p) K L := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← hof]
  have : Algebra.IsAlgebraic (MvPolynomial ℕ (ZMod p)) K :=
    IsLocalization.isAlgebraic K (nonZeroDivisors (MvPolynomial ℕ (ZMod p)))
  have : IsPRadical (algebraMap K L) p := hof ▸ PerfectClosure.isPRadical K p
  have : IsPurelyInseparable K L := IsPRadical.isPurelyInseparable K L p
  have htr : Algebra.trdeg (ZMod p) L = Cardinal.aleph0 := by
    have htbK := (IsTranscendenceBasis.mvPolynomial ℕ (ZMod p)).algebraMap_comp (A := K)
    have htbL := htbK.algebraMap_comp (A := L)
    simpa using htbL.cardinalMk_eq_trdeg.symm
  exact ⟨htr, perfectRing_summary p L⟩

end TauCeti.Examples
