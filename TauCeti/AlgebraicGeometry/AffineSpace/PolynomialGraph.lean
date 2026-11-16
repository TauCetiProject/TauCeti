/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import TauCeti.AlgebraicGeometry.AffineSpace.Basic
public import TauCeti.RingTheory.MvPolynomial.PolynomialGraph
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Nilpotent
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic

/-!
# Kronecker polynomial graphs in affine space and hypersurface avoidance

For a commutative ring `k` and natural numbers `m` and `B`, the spectrum of
`TauCeti.polynomialGraph k m B : MvPolynomial (Fin m) k →+* Polynomial k` is the Kronecker
polynomial graph morphism
`Spec (.of (Polynomial k)) ⟶ Spec (.of (MvPolynomial (Fin m) k))`
sending `t` to `(t, t ^ B, t ^ (B ^ 2), …, t ^ (B ^ (m - 1)))` over `Spec (.of k)`.

When `0 < m`, `polynomialGraph k m B` is surjective (`TauCeti.polynomialGraph_surjective`), so its
spectrum is a closed immersion of the affine line into affine `m`-space; for `1 ≤ B` it also maps
the origin `Spec.map Polynomial.constantCoeff` of `𝔸¹_k` to the origin
`Spec.map MvPolynomial.constantCoeff` of `𝔸^m_k`. Given any nonzero polynomial
`h : MvPolynomial (Fin m) k` with `0 < m`, choosing `B ≥ 2` larger than every exponent coordinate
in `h.support` yields a closed-immersion Kronecker graph along which `h` pulls back to a nonzero
univariate polynomial (`TauCeti.exists_avoiding_graph`). Over a reduced ring this makes the
preimage of the principal open `D(h)` nonempty, and over an integral domain it makes that preimage
a nonempty dense open of `𝔸¹_k`, without extending `k`.

## Main results

* `TauCeti.specMap_polynomialGraph_C`, `TauCeti.specMap_polynomialGraph_over`,
  `TauCeti.specMap_polynomialGraph_ulift_specIso_inv`,
  `TauCeti.specMap_polynomialGraph_specIso_inv`: compatibility of the Kronecker graph morphism with
  the `Spec (.of k)` structure maps and with `AlgebraicGeometry.AffineSpace.homOfAlgebra`.
* `TauCeti.specMap_constantCoeff_polynomialGraph`: for `1 ≤ B`, the Kronecker graph maps the origin
  of `𝔸¹_k` to the origin of `𝔸^m_k` (failing at `B = 0` when `2 ≤ m` over a nontrivial ring,
  `TauCeti.specMap_constantCoeff_polynomialGraph_zero_right_ne`).
* `TauCeti.isClosedImmersion_specMap_polynomialGraph`,
  `TauCeti.isClosedImmersion_specMap_polynomialGraph_iff`: for `0 < m`, the Kronecker graph is a
  closed immersion, and over a nontrivial ring it is a closed immersion if and only if `0 < m`
  (failing at `m = 0` by `TauCeti.not_isClosedImmersion_specMap_polynomialGraph_zero`).
* `TauCeti.exists_avoiding_graph`: for `0 < m` and `h ≠ 0`, there exists `B ≥ 2` exceeding all
  exponent coordinates in `h.support` such that `polynomialGraph k m B h ≠ 0` and
  `Spec.map (CommRingCat.ofHom (polynomialGraph k m B))` is a closed immersion.
* `TauCeti.nonempty_specMap_polynomialGraph_preimage_basicOpen_iff`,
  `TauCeti.dense_specMap_polynomialGraph_preimage_basicOpen`: nonemptiness over reduced rings and
  Zariski density over integral domains of the preimage of `PrimeSpectrum.basicOpen h` along the
  Kronecker graph.
* `TauCeti.specMap_polynomialGraph_preimage_basicOpen_X_one_sub_X_zero_pow_eq_bot`: for `2 ≤ m`,
  every fixed Kronecker graph misses `D(X 1 - X 0 ^ B)`, so `B` must depend on `h`.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  proof of Theorem 3.3.7 and Exercise 3.5(a), for the base-`B` Kronecker substitution
  `xᵢ ↦ t ^ (d ^ (i - 1))`.
* M. Kisin and R. Zhou, *Independence of `ℓ` for Frobenius conjugacy classes attached to abelian
  varieties*, arXiv:2103.09945v2, proofs of Corollary 5.2.7 (pp. 52–53) and Proposition 5.3.5
  (p. 54), for the motivating same-field curve-selection step (carried out there via Poonen's
  Bertini theorem rather than Kronecker graphs).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

section CommRing

variable {k : Type u} [CommRing k]

/-- Precomposing `Spec.map (polynomialGraph k m B)` on global sections with `MvPolynomial.C`
recovers `Spec.map Polynomial.C`. -/
@[reassoc (attr := simp)]
theorem specMap_polynomialGraph_C (m B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := k) (σ := Fin m))) =
      Spec.map (CommRingCat.ofHom (Polynomial.C (R := k))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, polynomialGraph_comp_C]

/-- The Kronecker graph `Spec.map (polynomialGraph k m B)` is a morphism of `Spec (.of k)`-schemes.
-/
@[reassoc]
theorem specMap_polynomialGraph_over (m B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin m) k))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) := by
  simp

/-- Under `(AffineSpace.SpecIso (ULift (Fin m)) (.of k)).inv`, the Kronecker graph agrees with
`AffineSpace.homOfAlgebra k` for the power tuple `i ↦ X ^ (B ^ i.down)`. -/
@[reassoc]
theorem specMap_polynomialGraph_ulift_specIso_inv (m B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ≫
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.rename (R := k) (ULift.down : ULift.{u} (Fin m) → Fin m) :
          MvPolynomial (ULift.{u} (Fin m)) k →+* MvPolynomial (Fin m) k)) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin m)) (.of k)).inv =
      AffineSpace.homOfAlgebra k
        (fun i : ULift.{u} (Fin m) ↦ (Polynomial.X : Polynomial k) ^ (B ^ (i.down : ℕ))) := by
  have h : (polynomialGraph k m B).comp
      (MvPolynomial.rename (R := k) (ULift.down : ULift.{u} (Fin m) → Fin m) :
        MvPolynomial (ULift.{u} (Fin m)) k →+* MvPolynomial (Fin m) k) =
      (MvPolynomial.aeval (R := k) (fun i : ULift.{u} (Fin m) ↦
        (Polynomial.X : Polynomial k) ^ (B ^ (i.down : ℕ))) :
        MvPolynomial (ULift.{u} (Fin m)) k →+* Polynomial k) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ by simp) fun i ↦ ?_
    simp
  rw [AffineSpace.homOfAlgebra_def, AlgHom.toRingHom_eq_coe, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, h]

/-- Over `k : Type`, composing `Spec.map (polynomialGraph k m B)` with
`(AffineSpace.SpecIso (Fin m) (.of k)).inv` recovers `AffineSpace.homOfAlgebra k` on
`i ↦ X ^ (B ^ i)`. -/
@[reassoc]
theorem specMap_polynomialGraph_specIso_inv {k : Type} [CommRing k] (m B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ≫
      (AffineSpace.SpecIso (Fin m) (.of k)).inv =
      AffineSpace.homOfAlgebra k
        (fun i : Fin m ↦ (Polynomial.X : Polynomial k) ^ (B ^ (i : ℕ))) := by
  simp [AffineSpace.homOfAlgebra_def]

/-- For `1 ≤ B`, the Kronecker graph maps the origin `Spec.map Polynomial.constantCoeff` of `𝔸¹_k`
to the origin `Spec.map MvPolynomial.constantCoeff` of `𝔸^m_k`. -/
@[reassoc]
theorem specMap_constantCoeff_polynomialGraph {m B : ℕ} (hB : 1 ≤ B) :
    Spec.map (CommRingCat.ofHom (Polynomial.constantCoeff (R := k))) ≫
      Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff (R := k))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, constantCoeff_comp_polynomialGraph hB]

/-- At `B = 0` and `2 ≤ m` over a nontrivial ring `k`, the Kronecker graph sends the origin of
`𝔸¹_k` to `(0, 1, …, 1)` rather than the origin of `𝔸^m_k`. -/
theorem specMap_constantCoeff_polynomialGraph_zero_right_ne {m : ℕ} (hm : 2 ≤ m) [Nontrivial k] :
    Spec.map (CommRingCat.ofHom (Polynomial.constantCoeff (R := k))) ≫
      Spec.map (CommRingCat.ofHom (polynomialGraph k m 0)) ≠
      Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff (R := k))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  intro h
  exact constantCoeff_comp_polynomialGraph_zero_right_ne hm
    (by simpa only [CommRingCat.hom_ofHom] using CommRingCat.hom_ext_iff.mp (Spec.map_injective h))

/-- When `0 < m`, the Kronecker graph `Spec.map (polynomialGraph k m B)` is a closed immersion of
`𝔸¹_k` into `𝔸^m_k` for every base `B`. -/
theorem isClosedImmersion_specMap_polynomialGraph {m : ℕ} (hm : 0 < m) (B : ℕ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) := by
  rw [IsClosedImmersion.SpecMap_iff, CommRingCat.hom_ofHom]
  exact polynomialGraph_surjective hm B

/-- Typeclass form of `isClosedImmersion_specMap_polynomialGraph` when `[NeZero m]` is in scope. -/
instance isClosedImmersion_specMap_polynomialGraph_of_neZero {m : ℕ} [NeZero m] (B : ℕ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) :=
  isClosedImmersion_specMap_polynomialGraph (NeZero.pos m) B

/-- At `m = 0` over a nontrivial ring `k`, `Spec.map (polynomialGraph k 0 B)` is the structural
projection `𝔸¹_k ⟶ Spec (.of k)`, which is not a closed immersion. -/
theorem not_isClosedImmersion_specMap_polynomialGraph_zero [Nontrivial k] (B : ℕ) :
    ¬ IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k 0 B))) := by
  simp [IsClosedImmersion.SpecMap_iff]

/-- Over a nontrivial commutative ring `k`, the Kronecker graph `Spec.map (polynomialGraph k m B)`
is a closed immersion if and only if `0 < m`. -/
theorem isClosedImmersion_specMap_polynomialGraph_iff [Nontrivial k] (m B : ℕ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) ↔ 0 < m := by
  simp [IsClosedImmersion.SpecMap_iff]

/-- **A Kronecker graph avoiding a hypersurface.** For `m > 0` and a nonzero polynomial `h` in `m`
variables over a commutative ring `k`, there is a base `B ≥ 2` exceeding every exponent coordinate
in the support of `h` such that `polynomialGraph k m B h ≠ 0` and the graph
`Spec (.of (Polynomial k)) ⟶ Spec (.of (MvPolynomial (Fin m) k))` is a closed immersion. -/
theorem exists_avoiding_graph {k : Type*} [CommRing k] {m : ℕ} (hm : 0 < m)
    {h : MvPolynomial (Fin m) k} (hh : h ≠ 0) :
    ∃ B : ℕ, 2 ≤ B ∧ (∀ d ∈ h.support, ∀ i, d i < B) ∧ polynomialGraph k m B h ≠ 0 ∧
      IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) := by
  obtain ⟨B, hB, hsupp, hne⟩ := exists_polynomialGraph_ne_zero hh
  exact ⟨B, hB, hsupp, hne, isClosedImmersion_specMap_polynomialGraph hm B⟩

/-- For `2 ≤ m`, every fixed Kronecker graph `Spec.map (polynomialGraph k m B)` maps all of `𝔸¹_k`
into the hypersurface `V(X 1 - X 0 ^ B)`, so the preimage of `D(X 1 - X 0 ^ B)` is empty. -/
theorem specMap_polynomialGraph_preimage_basicOpen_X_one_sub_X_zero_pow_eq_bot
    {m : ℕ} (hm : 2 ≤ m) (B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen
        (MvPolynomial.X ⟨1, hm⟩ - MvPolynomial.X ⟨0, by omega⟩ ^ B : MvPolynomial (Fin m) k) =
      ⊥ := by
  rw [SpecMap_preimage_basicOpen, CommRingCat.ofHom_apply]
  exact (PrimeSpectrum.basicOpen_eq_bot_iff _).mpr (by simp)

end CommRing

/-! ### Principal opens over reduced rings and integral domains -/

section ReducedAndDomain

variable {k : Type u} [CommRing k]

/-- Over a reduced commutative ring `k`, the preimage of the principal open
`PrimeSpectrum.basicOpen h` along `Spec.map (polynomialGraph k m B)` is nonempty if and only if
`polynomialGraph k m B h ≠ 0`. -/
theorem nonempty_specMap_polynomialGraph_preimage_basicOpen_iff [IsReduced k] (m B : ℕ)
    (h : MvPolynomial (Fin m) k) :
    (Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ PrimeSpectrum.basicOpen h :
      Set (Spec (.of (Polynomial k)))).Nonempty ↔
      polynomialGraph k m B h ≠ 0 := by
  rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty, SpecMap_preimage_basicOpen,
    CommRingCat.ofHom_apply]
  refine (PrimeSpectrum.basicOpen_eq_bot_iff _).not.trans
    (not_iff_not.mpr ⟨fun hnil ↦ ?_, fun h0 ↦ by simp [h0]⟩)
  ext i
  simpa using isNilpotent_iff_eq_zero.mp (Polynomial.isNilpotent_iff.mp hnil i)

/-- Over an integral domain `k`, whenever `polynomialGraph k m B h ≠ 0`, the preimage of
`PrimeSpectrum.basicOpen h` along `Spec.map (polynomialGraph k m B)` is Zariski dense in
`Spec (.of (Polynomial k))`. -/
theorem dense_specMap_polynomialGraph_preimage_basicOpen [IsDomain k] {m B : ℕ}
    {h : MvPolynomial (Fin m) k} (hne : polynomialGraph k m B h ≠ 0) :
    Dense (Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ PrimeSpectrum.basicOpen h :
      Set (Spec (.of (Polynomial k)))) :=
  (Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ PrimeSpectrum.basicOpen h).isOpen.dense
    ((nonempty_specMap_polynomialGraph_preimage_basicOpen_iff m B h).mpr hne)

end ReducedAndDomain

/-! ### Examples -/

section Examples

/-- Over `ZMod 4`, the hypothesis `[IsReduced k]` in
`nonempty_specMap_polynomialGraph_preimage_basicOpen_iff` cannot be dropped: `h = 2 X₀` is nonzero
and `polynomialGraph (ZMod 4) 1 2 h = 2 X ≠ 0`, yet `2 X` is nilpotent so the preimage of `D(h)` is
empty. -/
example :
    let h : MvPolynomial (Fin 1) (ZMod 4) := MvPolynomial.C 2 * MvPolynomial.X 0
    polynomialGraph (ZMod 4) 1 2 h ≠ 0 ∧
      Spec.map (CommRingCat.ofHom (polynomialGraph (ZMod 4) 1 2)) ⁻¹ᵁ
        PrimeSpectrum.basicOpen h = ⊥ := by
  dsimp only
  refine ⟨fun h0 ↦ ?_, ?_⟩
  · have hc : (2 : ZMod 4) = 0 := by simpa using congrArg (fun p ↦ p.coeff 1) h0
    exact absurd hc (by decide)
  · rw [SpecMap_preimage_basicOpen, CommRingCat.ofHom_apply]
    refine (PrimeSpectrum.basicOpen_eq_bot_iff _).mpr ⟨2, ?_⟩
    have h2 : (2 : ZMod 4) ^ 2 = 0 := by decide
    simp [mul_pow, ← Polynomial.C_pow, h2]

end Examples

end

end TauCeti
