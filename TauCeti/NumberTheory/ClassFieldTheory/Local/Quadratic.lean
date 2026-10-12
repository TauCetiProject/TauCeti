/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.CyclicClass
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Reciprocity

/-!
# The local Artin map of a quadratic extension

Let `K` be a nonarchimedean local field and `L/K` a quadratic extension, with nontrivial
automorphism `τ`. Its Galois group has two elements and is abelian, and the local Artin map
`localArtinMap K L ι : Kˣ → Gal(L/K)ᵃᵇ` is surjective with kernel the norm group `N_{L/K}(Lˣ)`.
Hence the Artin symbol of `a ∈ Kˣ` is trivial when `a` is a norm from `L` and is `τ` otherwise
(`localArtinMap_quadratic_eq_nontrivial_iff_not_norm`): the smallest nontrivial instance of the
norm-kernel theorem.

For `L = K(s)` with `s² = d`, the symbol–norm criterion `localSymbol_eq_zero_iff_mem_normGroup`
says that `a` is a norm from `L` exactly when the local symbol `(a, d)`, along the pairing
`kummerCupPairing ζ hζ` of the primitive square root of unity `ζ = -1`, vanishes. Combining the
two, the Artin symbol of `a` is `τ` exactly when `(a, d) = 1` in `ZMod 2`, that is, when the
quadratic Hilbert symbol `(a, d)_K` is `-1` (`localArtinMap_quadratic_eq_hilbertSymbol`). This
ties the Artin map of the local class formation to the cohomological Hilbert symbol.

## Main results

* `TauCeti.ClassFieldTheory.localArtinMap_quadratic_eq_nontrivial_iff_not_norm`: in a quadratic
  extension the Artin symbol of `a` is the nontrivial automorphism exactly when `a` is not a norm.
* `TauCeti.ClassFieldTheory.localArtinMap_quadratic_eq_hilbertSymbol`: for `L = K(√d)` the Artin
  symbol of `a` is the nontrivial automorphism exactly when the local symbol `(a, d)` is `1`.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter XIV,
  §§1–2.
* J. S. Milne, *Class Field Theory*, Chapter III, §4.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.IntermediateField Module

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The quadratic test of local reciprocity.** Let `L/K` be a quadratic Galois extension of a
nonarchimedean local field and `τ` its nontrivial automorphism. Then the local Artin symbol of
`a ∈ Kˣ` is `τ` exactly when `a` is not a norm from `L`; otherwise it is trivial
(`localArtinMap_eq_zero_iff`). -/
theorem localArtinMap_quadratic_eq_nontrivial_iff_not_norm (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (ι : L →ₐ[K] SeparableClosure K)
    (hdegree : finrank K L = 2) {τ : Gal(L/K)} (hτ : τ ≠ 1) (a : Kˣ) :
    localArtinMap K L ι (Additive.ofMul a) = Additive.ofMul (Abelianization.of τ) ↔
      a ∉ normGroup K L := by
  have hcard : Nat.card Gal(L/K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, hdegree]
  have : Fact (Nat.card Gal(L/K)).Prime := ⟨hcard ▸ Nat.prime_two⟩
  have : IsCyclic Gal(L/K) := isCyclic_of_prime_card rfl
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  -- the symbol of `a` is the class of some `σ`, and `σ` is either `1` or `τ`
  obtain ⟨σ, hσ⟩ := Abelianization.equivOfComm.surjective
    (localArtinMap K L ι (Additive.ofMul a)).toMul
  have hστ : σ ≠ 1 → σ = τ := fun h ↦ ((Nat.card_eq_two_iff' 1).1 hcard).unique h hτ
  rw [← localArtinMap_eq_zero_iff K L ι, ← ofMul_toMul (localArtinMap K L ι _), ← hσ]
  have heq : Additive.ofMul (Abelianization.equivOfComm σ) =
      Additive.ofMul (Abelianization.of τ) ↔ σ = τ := by
    simp [← Abelianization.equivOfComm_apply]
  have hone : Additive.ofMul (Abelianization.equivOfComm σ) = 0 ↔ σ = 1 := by
    simp [-Abelianization.equivOfComm_apply]
  rw [heq, hone]
  exact ⟨fun h ↦ h ▸ hτ, hστ⟩

/-- **The quadratic test against the local symbol.** Let `L = K(s)` with `s² = d`, Galois over
the nonarchimedean local field `K`, and let `τ` be a nontrivial automorphism of `L/K`, so that
`L/K` is quadratic and `τ s = -s`. Then the local Artin symbol of `a ∈ Kˣ` is `τ` exactly when
the local symbol `(a, d)` along `kummerCupPairing ζ hζ`, for the primitive square root of unity
`ζ = -1`, is `1`: classically, when the quadratic Hilbert symbol `(a, d)_K` is `-1`. The
identification `tr : H²(G_K, μ₂) ≃+ ZMod 2` is arbitrary, and the Kummer classes use the
invertibility of `2` in `K` supplied by `ζ`. -/
theorem localArtinMap_quadratic_eq_hilbertSymbol {L : Type} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (ι : L →ₐ[K] SeparableClosure K) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 2) (tr : continuousCohomology 2 (muNRep 2 K) ≃+ ZMod 2) {d : Kˣ}
    {s : L} (hs : s ^ 2 = algebraMap K L d) (hgen : K⟮s⟯ = ⊤) {τ : Gal(L/K)} (hτ : τ ≠ 1)
    (a : Kˣ) :
    localArtinMap K L ι (Additive.ofMul a) = Additive.ofMul (Abelianization.of τ) ↔
      localSymbol (kummerCupPairing ζ hζ) tr (kummerClass K hζ.neZero'.out.isUnit a)
        (kummerClass K hζ.neZero'.out.isUnit d) = 1 := by
  -- `[L : K]` divides `2`, and it is not `1` because `τ ≠ 1`
  obtain ⟨-, -, hdvd, -⟩ := exists_forall_mem_zpowers_apply_eq hζ d.ne_zero hs hgen
  have hdegree : finrank K L = 2 := by
    refine ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left fun h ↦ hτ ?_
    have : Subsingleton Gal(L/K) := (Nat.card_eq_one_iff_unique.1 <| by
      rw [IsGalois.card_aut_eq_finrank, h]).1
    exact Subsingleton.elim _ _
  rw [localArtinMap_quadratic_eq_nontrivial_iff_not_norm K L ι hdegree hτ,
    ← localSymbol_eq_zero_iff_mem_normGroup hζ tr hζ.neZero'.out.isUnit a d hs hgen]
  -- in `ZMod 2`, the nonzero element is `1`
  exact (by decide : ∀ x : ZMod 2, ¬x = 0 ↔ x = 1) _

end TauCeti.ClassFieldTheory
